import os
import re
import time
import json
import asyncio
import logging
import requests
import tempfile
from datetime import datetime, timedelta

import discord
import gspread
from gspread.utils import rowcol_to_a1
import google.generativeai as genai
from google.api_core.exceptions import ResourceExhausted
from google.oauth2.service_account import Credentials
from PIL import Image

# ── Logging ───────────────────────────────────────────────────────────────────
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger(__name__)

# ── Config from environment ───────────────────────────────────────────────────
DISCORD_TOKEN          = os.environ["DISCORD_TOKEN"]
DISCORD_CHANNEL_ID     = int(os.environ["DISCORD_CHANNEL_ID"])
GEMINI_API_KEY         = os.environ["GEMINI_API_KEY"]
GOOGLE_SHEET_ID        = os.environ["GOOGLE_SHEET_ID"]
GOOGLE_CREDENTIALS     = os.environ["GOOGLE_CREDENTIALS"]
GEMINI_2ND_RUN         = int(os.environ.get("GEMINI_2ND_RUN", "0"))       # 0=off 1=bei Fehler 2=immer
GEMINI_BACKOFF_MINUTES = int(os.environ.get("GEMINI_BACKOFF_MINUTES", "60"))

POLL_INTERVAL = 15
DONE_EMOJI    = "\u2705"
ERROR_EMOJI   = "\u274c"

# Gemini-Quota-Sperre (in-memory, wird gesetzt wenn Kontingent erschoepft)
gemini_blocked_until = None

class GeminiQuotaError(Exception):
    pass

# ── Sheet-Layout ───────────────────────────────────────────────────────────────
# Rennen 1 startet in Spalte B (Index 2), Abstand 16 Spalten pro Rennen
# Zeilen pro Grid-Block: 20 (Block 0 = Zeilen 5-24, Block 1 = 25-44, usw.)
# Fastest-Lap-Zeile: 3
#
# Relative Spalten innerhalb eines Rennblocks (0-basiert von Spalte B):
#   0 = B  Grid-Label
#   1 = C  Position
#   2 = D  Driver
#   3 = E  Team (nicht befuellt)
#   4 = F  Car  / Fastest-Lap-Fahrer (Zeile 3)
#   5 = G  RaceTime / Fastest-Lap-Zeit (Zeile 3)
#   6 = H  +L

COL_OFFSET_PER_RACE  = 14
ROW_OFFSET_PER_GRID  = 20
FIRST_DATA_ROW       = 5
FIRST_COL_RACE1      = 2
FASTEST_LAP_ROW      = 3

REL = {
    "grid_label": 0,
    "position":   1,
    "driver":     2,
    "car":        4,
    "racetime":   5,
    "laps":       6,
    "fl_driver":  4,
    "fl_time":    5,
}

# ── Sheet-Koordinaten ─────────────────────────────────────────────────────────
def col_start(rennen):
    return FIRST_COL_RACE1 + (rennen - 1) * COL_OFFSET_PER_RACE

def row_start(block):
    return FIRST_DATA_ROW + block * ROW_OFFSET_PER_GRID

def get_cell(rennen, block, position, field):
    c = col_start(rennen) + REL[field]
    r = row_start(block) + (position - 1)
    return r, c

def get_grid_label_cell(rennen, block):
    return row_start(block), col_start(rennen) + REL["grid_label"]

# ── Google Sheets ─────────────────────────────────────────────────────────────
def get_sheet():
    creds_dict = json.loads(GOOGLE_CREDENTIALS)
    scopes = [
        "https://www.googleapis.com/auth/spreadsheets",
        "https://www.googleapis.com/auth/drive",
    ]
    creds = Credentials.from_service_account_info(creds_dict, scopes=scopes)
    client = gspread.authorize(creds)
    return client.open_by_key(GOOGLE_SHEET_ID).sheet1

def read_grid_label(sheet, rennen, block):
    r, c = get_grid_label_cell(rennen, block)
    val = sheet.cell(r, c).value
    return (val or "").strip().lower()

def resolve_block(sheet, rennen, grid_label):
    """
    Ermittelt den Ziel-Block (0-basiert).
    Ausgangspunkt ist immer 3-Grid-Annahme:
      Block 0 -> Grid 1
      Block 1 -> Grid 2 / 2a
      Block 2 -> Grid 3  (oder 2b wenn 3 schon da ist)
      Block 3 -> Grid 3  (wenn 2b in Block 2 eingetragen wurde)
    """
    gl = grid_label.strip().lower()

    if gl == "1":
        return 0
    if gl in ("2", "2a"):
        return 1

    label_block2 = read_grid_label(sheet, rennen, 2)

    if gl == "3":
        if label_block2 == "2b":
            return 3
        return 2

    if gl == "2b":
        if label_block2 == "3":
            log.info(f"Rennen {rennen}: Grid 3 in Block 2, verschiebe nach Block 3")
            shift_block(sheet, rennen, src_block=2, dst_block=3)
        return 2

    log.warning(f"Unbekanntes Grid-Label '{grid_label}', verwende Block 2")
    return 2

def shift_block(sheet, rennen, src_block, dst_block):
    """Verschiebt alle Daten eines Blocks in einen anderen."""
    sr, sc = get_grid_label_cell(rennen, src_block)
    dr, dc = get_grid_label_cell(rennen, dst_block)
    sheet.update_cell(dr, dc, sheet.cell(sr, sc).value or "")
    sheet.update_cell(sr, sc, "")
    time.sleep(0.2)

    for pos in range(1, 21):
        for field in ("driver", "car", "racetime", "laps"):
            sr2, sc2 = get_cell(rennen, src_block, pos, field)
            dr2, dc2 = get_cell(rennen, dst_block, pos, field)
            sheet.update_cell(dr2, dc2, sheet.cell(sr2, sc2).value or "")
            sheet.update_cell(sr2, sc2, "")
            time.sleep(0.1)

# ── Zeit-Formatierung ─────────────────────────────────────────────────────────
def clean_time(zeit):
    """Gibt (racetime_digits, laps) zurueck."""
    if not zeit:
        return None, None
    z = zeit.strip()
    if z.upper() == "DNF" or re.match(r"^[-:,\.]+$", z):
        return None, None
    m = re.match(r"^(\d+)\s*(Runden?|Laps?)$", z, re.IGNORECASE)
    if m:
        return None, m.group(1)
    digits = re.sub(r"[^\d]", "", z)
    return (digits if digits else None), None

# ── Delta-Validierung ─────────────────────────────────────────────────────────
def validate_deltas(fahrer_list):
    """Gibt Positionen zurueck bei denen das Delta nicht groesser als das vorherige ist."""
    errors = []
    prev_delta = None
    for f in sorted(fahrer_list, key=lambda x: x["position"]):
        pos = f["position"]
        if pos == 1:
            continue
        racetime, laps = clean_time(f.get("zeit", ""))
        if racetime is None:
            continue
        try:
            delta = int(racetime)
        except ValueError:
            continue
        if prev_delta is not None and delta <= prev_delta:
            errors.append(pos)
            log.warning(f"Delta-Fehler P{pos}: {delta} <= {prev_delta}")
        prev_delta = delta
    return errors

def mark_red(sheet, rennen, block, position):
    r, c = get_cell(rennen, block, position, "racetime")
    cell_addr = rowcol_to_a1(r, c)
    sheet.format(cell_addr, {
        "textFormat": {
            "foregroundColor": {"red": 1.0, "green": 0.0, "blue": 0.0}
        }
    })

# ── Schnellste Runde ──────────────────────────────────────────────────────────
def update_fastest_lap(sheet, rennen, new_driver, new_time_int):
    """Traegt schnellste Runde in Zeile 3 ein, wenn sie schneller als die aktuelle ist."""
    c_driver = col_start(rennen) + REL["fl_driver"]
    c_time   = col_start(rennen) + REL["fl_time"]

    current_val = sheet.cell(FASTEST_LAP_ROW, c_time).value
    if current_val:
        current_digits = re.sub(r"[^\d]", "", str(current_val))
        if current_digits and int(current_digits) <= new_time_int:
            return

    log.info(f"Neue schnellste Runde: {new_driver} - {new_time_int}")
    sheet.update_cell(FASTEST_LAP_ROW, c_driver, new_driver)
    sheet.update_cell(FASTEST_LAP_ROW, c_time, str(new_time_int))

# ── Gemini ────────────────────────────────────────────────────────────────────
genai.configure(api_key=GEMINI_API_KEY)
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.0-flash")
gemini_model = genai.GenerativeModel(GEMINI_MODEL)
GENERATION_CONFIG = genai.GenerationConfig(temperature=0)

PROMPT_EXTRACT = (
    "Analysiere diesen Gran Turismo Ergebnisscreen und extrahiere die Daten als JSON.\n\n"
    "Gib NUR gueltiges JSON zurueck, kein Markdown, keine Erklaerungen.\n\n"
    "WICHTIG: Kopiere alle Texte (Fahrernamen, Autonamen) EXAKT so wie sie im Bild stehen.\n"
    "Korrigiere NIEMALS Schreibweise, Gross-/Kleinschreibung, Sonderzeichen oder Tippfehler.\n"
    "Fahrernamen sind Online-Nicknames und koennen ungewoehnliche Schreibweisen haben.\n"
    "Beispiel: 'Bismark' bleibt 'Bismark', NICHT 'Bismarck'.\n"
    "Beispiel: 'XxChillerHDxX95' bleibt exakt so, NICHT vereinfacht.\n\n"
    "Format:\n"
    "{\n"
    '  "rennen": <Zahl>,\n'
    '  "grid": "<Grid-Label als String: 1, 2, 2a, 2b oder 3>",\n'
    '  "fahrer": [\n'
    "    {\n"
    '      "position": <Zahl>,\n'
    '      "name": "<Fahrername exakt wie im Bild>",\n'
    '      "auto": "<Autoname exakt wie im Bild>",\n'
    '      "zeit": "<Zeitstring exakt wie im Bild>",\n'
    '      "beste_runde": "<Rundenzeit aus Spalte BESTE RUNDE, z.B. 8:27,088, oder leer>"\n'
    "    }\n"
    "  ]\n"
    "}\n\n"
    "Hinweise:\n"
    "- rennen und grid stehen im Titel, z.B. 'Rennen 16 - Grid 3' oder 'Grid 2a'\n"
    "- grid ist immer ein String\n"
    "- Der Erstplatzierte hat eine absolute Rennzeit (z.B. 50:28,752)\n"
    "- Alle anderen haben ein Delta (z.B. +06,425 oder +1:13,995)\n"
    "- Bei ueberrundeten Fahrern steht X Runden oder X Laps als Zeit\n"
    "- Bei DNF steht DNF oder --:--,--- als Zeit\n"
    "- beste_runde ist die Rundenzeit in der Spalte BESTE RUNDE ganz rechts\n"
)

PROMPT_VERIFY_TEMPLATE = (
    "Ich habe aus diesem Gran Turismo Screenshot folgende Daten extrahiert:\n\n"
    "{extracted}\n\n"
    "Vergleiche diese Daten sorgfaeltig mit dem Bild.\n"
    "Gib das (ggf. korrigierte) JSON zurueck. Gib NUR gueltiges JSON zurueck, kein Markdown.\n\n"
    "Regeln:\n"
    "- Aendere NUR was eindeutig falsch ist\n"
    "- Korrigiere NIEMALS Schreibweise von Fahrernamen oder Autonamen\n"
    "- Alle Texte muessen EXAKT wie im Bild stehen\n"
    "- Wenn alles korrekt ist, gib exakt dieselben Daten zurueck\n"
)

def call_gemini(img, prompt):
    global gemini_blocked_until
    try:
        response = gemini_model.generate_content(
            [prompt, img],
            generation_config=GENERATION_CONFIG
        )
        text = response.text.strip()
        text = re.sub(r"^```json\s*", "", text)
        text = re.sub(r"\s*```$", "", text)
        return json.loads(text)
    except ResourceExhausted as e:
        log.error(f"Gemini ResourceExhausted - Details: {str(e)}")
        gemini_blocked_until = datetime.now() + timedelta(minutes=GEMINI_BACKOFF_MINUTES)
        log.error(f"Gemini-Kontingent erschoepft. Sperre fuer {GEMINI_BACKOFF_MINUTES} Minuten.")
        raise GeminiQuotaError("Gemini-Kontingent erschoepft") from e
    except Exception as e:
        log.error(f"Gemini unerwarteter Fehler ({type(e).__name__}): {str(e)}")
        raise

def gemini_is_blocked():
    """Prueft ob die Gemini-Sperre noch aktiv ist."""
    global gemini_blocked_until
    if gemini_blocked_until is None:
        return False
    if datetime.now() >= gemini_blocked_until:
        gemini_blocked_until = None
        log.info("Gemini-Sperre aufgehoben.")
        return False
    return True

def analyse_image(image_path):
    img = Image.open(image_path)

    data = call_gemini(img, PROMPT_EXTRACT)
    log.info(f"Durchlauf 1: Rennen {data.get('rennen')}, Grid {data.get('grid')}, "
             f"{len(data.get('fahrer', []))} Fahrer")

    if GEMINI_2ND_RUN == 0:
        return data

    run_second = False
    if GEMINI_2ND_RUN == 2:
        run_second = True
    elif GEMINI_2ND_RUN == 1:
        errors = validate_deltas(data.get("fahrer", []))
        run_second = len(errors) > 0

    if run_second:
        log.info("Starte Durchlauf 2 (Verifikation)...")
        verify_prompt = PROMPT_VERIFY_TEMPLATE.format(
            extracted=json.dumps(data, ensure_ascii=False, indent=2)
        )
        data2 = call_gemini(img, verify_prompt)

        for f1, f2 in zip(data.get("fahrer", []), data2.get("fahrer", [])):
            for key in ("name", "auto", "zeit", "beste_runde"):
                if f1.get(key) != f2.get(key):
                    log.warning(f"  Abweichung P{f1['position']} [{key}]: "
                                f"'{f1.get(key)}' -> '{f2.get(key)}'")

        log.info("Durchlauf 2 abgeschlossen")
        data = data2

    return data

# ── Ergebnisse ins Sheet schreiben ────────────────────────────────────────────
def write_results(sheet, data):
    """
    Schreibt Ergebnisse ins Sheet.
    Gibt Liste von Discord-Warnmeldungen zurueck.
    """
    rennen      = int(data["rennen"])
    grid_label  = str(data["grid"]).strip()
    fahrer_list = data["fahrer"]
    warnings    = []

    block = resolve_block(sheet, rennen, grid_label)
    log.info(f"Rennen {rennen}, Grid '{grid_label}' -> Block {block}")

    r, c = get_grid_label_cell(rennen, block)
    sheet.update_cell(r, c, grid_label)
    time.sleep(0.2)

    delta_errors = validate_deltas(fahrer_list)

    fastest_time_int   = None
    fastest_lap_driver = None

    for fahrer in sorted(fahrer_list, key=lambda x: x["position"]):
        pos         = int(fahrer["position"])
        name        = fahrer["name"]
        auto        = fahrer["auto"]
        zeit        = fahrer.get("zeit", "")
        beste_runde = fahrer.get("beste_runde", "")

        racetime, laps = clean_time(zeit)

        log.info(f"  P{pos} {name} | {auto} | racetime={racetime} "
                 f"laps={laps} fl={beste_runde}")

        sheet.update_cell(*get_cell(rennen, block, pos, "driver"),   name)
        time.sleep(0.1)
        sheet.update_cell(*get_cell(rennen, block, pos, "car"),      auto)
        time.sleep(0.1)
        sheet.update_cell(*get_cell(rennen, block, pos, "racetime"), racetime or "")
        time.sleep(0.1)
        sheet.update_cell(*get_cell(rennen, block, pos, "laps"),     laps or "")
        time.sleep(0.1)

        if pos in delta_errors:
            mark_red(sheet, rennen, block, pos)
            time.sleep(0.1)
            warnings.append(
                f"Grid {grid_label}, Pos {pos}, {name}: Zeit ist zu pruefen"
            )

        if laps is not None:
            warnings.append(
                f"Grid {grid_label}, Pos {pos}, {name}: Zeit muss manuell eingetragen werden."
            )

        if beste_runde:
            br_digits = re.sub(r"[^\d]", "", beste_runde)
            if br_digits:
                br_int = int(br_digits)
                if fastest_time_int is None or br_int < fastest_time_int:
                    fastest_time_int   = br_int
                    fastest_lap_driver = name

    if fastest_lap_driver and fastest_time_int is not None:
        update_fastest_lap(sheet, rennen, fastest_lap_driver, fastest_time_int)

    return warnings

# ── Discord Bot ───────────────────────────────────────────────────────────────
intents = discord.Intents.default()
intents.message_content = True
intents.reactions = True

discord_client = discord.Client(intents=intents)

async def already_processed(message):
    for reaction in message.reactions:
        if str(reaction.emoji) in (DONE_EMOJI, ERROR_EMOJI):
            async for user in reaction.users():
                if user.id == discord_client.user.id:
                    return True
    return False

async def process_image(message, attachment):
    log.info(f"Verarbeite: {attachment.filename} von {message.author}")
    channel = message.channel
    started = asyncio.get_event_loop().time()

    with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
        tmp_path = f.name

    try:
        img_data = requests.get(attachment.url).content
        with open(tmp_path, "wb") as f:
            f.write(img_data)

        data     = analyse_image(tmp_path)
        sheet    = get_sheet()
        warnings = write_results(sheet, data)

        for w in warnings:
            await channel.send(w)

        await message.add_reaction(DONE_EMOJI)
        elapsed = asyncio.get_event_loop().time() - started
        log.info(f"Erfolgreich verarbeitet in {elapsed:.1f}s. {len(warnings)} Warnung(en).")

    except GeminiQuotaError:
        # Kein Error-Emoji setzen – Bild soll spaeter nochmal verarbeitet werden
        await channel.send(
            f"Gemini-Tageskontingent erschoepft. Auswertung pausiert fuer ca. {GEMINI_BACKOFF_MINUTES} Minuten. "
            f"Bild wird dann automatisch verarbeitet."
        )
        log.warning("Verarbeitung wegen Quota-Fehler abgebrochen, kein Emoji gesetzt.")

    except Exception as e:
        log.error(f"Fehler: {e}", exc_info=True)
        await message.add_reaction(ERROR_EMOJI)

    finally:
        elapsed = asyncio.get_event_loop().time() - started
        os.unlink(tmp_path)

    return elapsed

async def scan_channel():
    await discord_client.wait_until_ready()
    channel = discord_client.get_channel(DISCORD_CHANNEL_ID)

    if channel is None:
        log.error(f"Channel {DISCORD_CHANNEL_ID} nicht gefunden!")
        return

    log.info(f"Scanne #{channel.name} alle {POLL_INTERVAL}s | GEMINI_2ND_RUN={GEMINI_2ND_RUN}")

    while not discord_client.is_closed():
        try:
            # Wenn Gemini gesperrt ist, Scan komplett ueberspringen
            if gemini_is_blocked():
                log.info(f"Gemini gesperrt, ueberspringe Scan. Noch ca. {int((gemini_blocked_until - datetime.now()).total_seconds() / 60)} Minuten.")
                await asyncio.sleep(POLL_INTERVAL)
                continue

            async for message in channel.history(limit=50):
                attachments = [
                    a for a in message.attachments
                    if a.content_type and a.content_type.startswith("image/")
                ]
                if not attachments:
                    continue
                if await already_processed(message):
                    continue

                elapsed = await process_image(message, attachments[0])

                # Nach Quota-Fehler sofort Scan-Schleife verlassen
                if gemini_is_blocked():
                    break

                # Mindestens POLL_INTERVAL Sekunden zwischen zwei Auswertungen
                remaining = POLL_INTERVAL - (elapsed or 0)
                if remaining > 0:
                    log.info(f"Warte noch {remaining:.1f}s (Durchlauf dauerte {elapsed:.1f}s)")
                    await asyncio.sleep(remaining)

        except Exception as e:
            log.error(f"Scan-Fehler: {e}", exc_info=True)

        await asyncio.sleep(POLL_INTERVAL)

# ── Webserver (Render keep-alive) ─────────────────────────────────────────────
from aiohttp import web

async def handle(request):
    return web.Response(text="Bot laeuft.")

async def start_webserver():
    app = web.Application()
    app.router.add_get("/", handle)
    runner = web.AppRunner(app)
    await runner.setup()
    port = int(os.environ.get("PORT", 8080))
    site = web.TCPSite(runner, "0.0.0.0", port)
    await site.start()
    log.info(f"Webserver auf Port {port}")

@discord_client.event
async def on_ready():
    log.info(f"Eingeloggt als {discord_client.user}")
    discord_client.loop.create_task(scan_channel())

async def main():
    await start_webserver()
    await discord_client.start(DISCORD_TOKEN)

if __name__ == "__main__":
    asyncio.run(main())

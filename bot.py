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
GEMINI_2ND_RUN         = int(os.environ.get("GEMINI_2ND_RUN", "0"))
GEMINI_BACKOFF_MINUTES = int(os.environ.get("GEMINI_BACKOFF_MINUTES", "60"))

POLL_INTERVAL = 15
DONE_EMOJI    = "\u2705"
ERROR_EMOJI   = "\u274c"

NUMBER_EMOJIS = ["1\ufe0f\u20e3", "2\ufe0f\u20e3", "3\ufe0f\u20e3", "4\ufe0f\u20e3",
                 "5\ufe0f\u20e3", "6\ufe0f\u20e3", "7\ufe0f\u20e3", "8\ufe0f\u20e3",
                 "9\ufe0f\u20e3", "\U0001f51f"]

# Gemini-Quota-Sperre
gemini_blocked_until = None

# In-memory Fahrzeugliste (wird beim Start und bei !update geladen)
car_list = []

class GeminiQuotaError(Exception):
    pass

# ── Sheet-Layout ───────────────────────────────────────────────────────────────
# Blatt "T":       Ergebnisse
# Blatt "DB_Tech": Fahrzeugliste Spalte R ab Zeile 8
# Blatt "DB_drvr": Fahrerliste Spalte C ab Zeile 5
#
# Rennen 1 startet in Spalte B (Index 2), Abstand 14 Spalten pro Rennen
# Zeilen pro Grid-Block: 20
# Fastest-Lap-Zeile: 3
# Datum: D3, Track: E3, Drivers: B4 (zusammengefuehrt)
#
# REL (0-basiert von Rennen-Startspalte):
#   0 = Grid-Label
#   1 = Position
#   2 = Driver
#   4 = Car / FL-Fahrer (Zeile 3)
#   5 = RaceTime / FL-Zeit (Zeile 3)
#   6 = +L

COL_OFFSET_PER_RACE = 14
ROW_OFFSET_PER_GRID = 20
FIRST_DATA_ROW      = 5
FIRST_COL_RACE1     = 2
FASTEST_LAP_ROW     = 3

REL = {
    "grid_label": 0,
    "position":   1,
    "driver":     2,
    "team":       3,
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

# ── Google Sheets Client ──────────────────────────────────────────────────────
def get_gspread_client():
    creds_dict = json.loads(GOOGLE_CREDENTIALS)
    scopes = [
        "https://www.googleapis.com/auth/spreadsheets",
        "https://www.googleapis.com/auth/drive",
    ]
    creds = Credentials.from_service_account_info(creds_dict, scopes=scopes)
    return gspread.authorize(creds)

def get_sheet():
    """Gibt Tabellenblatt 'T' zurueck."""
    return get_gspread_client().open_by_key(GOOGLE_SHEET_ID).worksheet("T")

def get_workbook():
    """Gibt die gesamte Arbeitsmappe zurueck."""
    return get_gspread_client().open_by_key(GOOGLE_SHEET_ID)

# ── Fahrzeug- und Fahrerliste laden ──────────────────────────────────────────
def load_car_list():
    """Laedt Fahrzeugliste aus DB_Tech, Spalte R ab Zeile 8."""
    global car_list
    try:
        wb    = get_workbook()
        sheet = wb.worksheet("DB_tech")
        # Begrenzten Bereich lesen (R8:R300) statt gesamte Spalte
        vals  = sheet.get("R8:R300")
        car_list = [row[0].strip() for row in vals if row and row[0].strip()]
        if not car_list:
            log.warning("Fahrzeugliste ist leer! Bitte DB_Tech pruefen (Spalte R ab Zeile 8).")
        else:
            log.info(f"Fahrzeugliste geladen: {len(car_list)} Eintraege")
    except Exception as e:
        log.error(f"KRITISCH: Fahrzeugliste konnte nicht geladen werden: {e}")
        car_list = []

def load_driver_list():
    """Laedt Fahrerliste aus DB_drvr, Spalte C (Name) und K (Team) ab Zeile 5.
    Gibt dict {lower_name: (original_name, team)} zurueck."""
    try:
        wb     = get_workbook()
        sheet  = wb.worksheet("DB_drvr")
        # Namen und Teams in einem Aufruf lesen
        rows   = sheet.get("C5:K200")
        result = {}
        for row in rows:
            name = row[0].strip() if len(row) > 0 else ""
            team = row[8].strip() if len(row) > 8 else ""  # K ist Index 8 in C:K
            if name:
                result[name.lower()] = (name, team)
        if not result:
            log.warning("Fahrerliste ist leer! Bitte DB_drvr pruefen (Spalte C ab Zeile 5).")
        else:
            log.info(f"Fahrerliste geladen: {len(result)} Eintraege")
        return result
    except Exception as e:
        log.error(f"KRITISCH: Fahrerliste konnte nicht geladen werden: {e}")
        return {}

# ── Grid-Block Aufloesung ─────────────────────────────────────────────────────
def read_grid_label(sheet, rennen, block):
    r, c = get_grid_label_cell(rennen, block)
    val  = sheet.cell(r, c).value
    return (val or "").strip().lower()

def resolve_block(sheet, rennen, grid_label):
    gl = grid_label.strip().lower()
    if gl == "1":
        return 0
    if gl in ("2", "2a"):
        return 1
    label_block2 = read_grid_label(sheet, rennen, 2)
    if gl == "3":
        return 3 if label_block2 == "2b" else 2
    if gl == "2b":
        if label_block2 == "3":
            log.info(f"Rennen {rennen}: Grid 3 in Block 2, verschiebe nach Block 3")
            shift_block(sheet, rennen, src_block=2, dst_block=3)
        return 2
    log.warning(f"Unbekanntes Grid-Label '{grid_label}', verwende Block 2")
    return 2

def shift_block(sheet, rennen, src_block, dst_block):
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
    """Gibt (racetime_int_or_None, laps_int_or_None) zurueck. Zeiten als Integer (kein Apostroph)."""
    if not zeit:
        return None, None
    z = zeit.strip()
    if z.upper() == "DNF" or re.match(r"^[-:,\.]+$", z):
        return None, None
    m = re.match(r"^(\d+)\s*(Runden?|Laps?)$", z, re.IGNORECASE)
    if m:
        return None, int(m.group(1))
    digits = re.sub(r"[^\d]", "", z)
    return (int(digits) if digits else None), None

# ── Delta-Validierung ─────────────────────────────────────────────────────────
def validate_deltas(fahrer_list):
    errors     = []
    prev_delta = None
    for f in sorted(fahrer_list, key=lambda x: x["position"]):
        pos = f["position"]
        if pos == 1:
            continue
        racetime, laps = clean_time(f.get("zeit", ""))
        if racetime is None:
            continue
        if prev_delta is not None and racetime <= prev_delta:
            errors.append(pos)
            log.warning(f"Delta-Fehler P{pos}: {racetime} <= {prev_delta}")
        prev_delta = racetime
    return errors

def mark_cell_red(sheet, row, col):
    sheet.format(rowcol_to_a1(row, col), {
        "textFormat": {"foregroundColor": {"red": 1.0, "green": 0.0, "blue": 0.0}}
    })

# ── Schnellste Runde ──────────────────────────────────────────────────────────
def update_fastest_lap(sheet, rennen, new_driver, new_time_int):
    c_driver    = col_start(rennen) + REL["fl_driver"]
    c_time      = col_start(rennen) + REL["fl_time"]
    current_val = sheet.cell(FASTEST_LAP_ROW, c_time).value
    if current_val:
        current_digits = re.sub(r"[^\d]", "", str(current_val))
        if current_digits and int(current_digits) <= new_time_int:
            return
    log.info(f"Neue schnellste Runde: {new_driver} - {new_time_int}")
    sheet.update_cell(FASTEST_LAP_ROW, c_driver, new_driver)
    sheet.update_cell(FASTEST_LAP_ROW, c_time,   new_time_int)  # Integer, kein Apostroph

# ── Gemini ────────────────────────────────────────────────────────────────────
genai.configure(api_key=GEMINI_API_KEY)
GEMINI_MODEL      = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash")
gemini_model      = genai.GenerativeModel(GEMINI_MODEL)
GENERATION_CONFIG = genai.GenerationConfig(temperature=0)

def build_extract_prompt():
    """Erstellt den Extraktions-Prompt mit aktueller Fahrzeugliste."""
    car_list_str = "\n".join(f"- {c}" for c in car_list) if car_list else "(keine Liste verfuegbar)"
    return (
        "Analysiere diesen Gran Turismo Ergebnisscreen und extrahiere die Daten als JSON.\n\n"
        "Gib NUR gueltiges JSON zurueck, kein Markdown, keine Erklaerungen.\n\n"
        "FAHRERNAMEN: Kopiere exakt so wie im Bild. Keine Korrekturen.\n"
        "Beispiel: 'Bismark' bleibt 'Bismark', 'XxChillerHDxX95' bleibt exakt so.\n\n"
        "FAHRZEUGNAMEN: Nutze IMMER den passenden Namen aus dieser Liste:\n"
        f"{car_list_str}\n\n"
        "Matching-Regeln fuer Fahrzeuge:\n"
        "- Nutze dein Wissen ueber Hersteller (z.B. Huracan = Lamborghini)\n"
        "- Die Jahreszahl ('22, '15 etc.) MUSS exakt uebereinstimmen\n"
        "- Pruefe die KOMPLETTE Liste, nicht nur den ersten Treffer\n"
        "- Wenn kein passender Eintrag: Originalnamen behalten, 'auto_unbekannt': true\n\n"
        "Format:\n"
        "{\n"
        '  "rennen": <Zahl>,\n'
        '  "grid": "<1, 2, 2a, 2b oder 3>",\n'
        '  "fahrer": [\n'
        "    {\n"
        '      "position": <Zahl>,\n'
        '      "name": "<exakt wie im Bild>",\n'
        '      "auto": "<Name aus Liste oder Original>",\n'
        '      "auto_unbekannt": <true oder false>,\n'
        '      "zeit": "<exakt wie im Bild>",\n'
        '      "beste_runde": "<z.B. 8:27,088 oder leer>"\n'
        "    }\n"
        "  ]\n"
        "}\n\n"
        "Hinweise:\n"
        "- rennen und grid stehen im Titel\n"
        "- Erstplatzierter hat absolute Rennzeit (z.B. 50:28,752)\n"
        "- Alle anderen haben Delta (z.B. +06,425)\n"
        "- Ueberrundete Fahrer: 'X Runden' oder 'X Laps'\n"
        "- DNF: 'DNF' oder '--:--,---'\n"
        "- beste_runde aus Spalte BESTE RUNDE ganz rechts\n"
    )

PROMPT_VERIFY_TEMPLATE = (
    "Ich habe aus diesem Gran Turismo Screenshot folgende Daten extrahiert:\n\n"
    "{extracted}\n\n"
    "Vergleiche sorgfaeltig mit dem Bild und gib korrigiertes JSON zurueck.\n"
    "Gib NUR gueltiges JSON zurueck, kein Markdown.\n\n"
    "Regeln:\n"
    "- Aendere NUR was eindeutig falsch ist\n"
    "- Fahrernamen NIEMALS korrigieren\n"
    "- Wenn alles korrekt, exakt dieselben Daten zurueckgeben\n"
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
        text = re.sub(r"\s*```$",     "", text)
        return json.loads(text)
    except ResourceExhausted as e:
        log.error(f"Gemini ResourceExhausted: {str(e)}")
        gemini_blocked_until = datetime.now() + timedelta(minutes=GEMINI_BACKOFF_MINUTES)
        log.error(f"Gemini-Sperre fuer {GEMINI_BACKOFF_MINUTES} Minuten.")
        raise GeminiQuotaError("Gemini-Kontingent erschoepft") from e
    except Exception as e:
        log.error(f"Gemini Fehler ({type(e).__name__}): {str(e)}")
        raise

def gemini_is_blocked():
    global gemini_blocked_until
    if gemini_blocked_until is None:
        return False
    if datetime.now() >= gemini_blocked_until:
        gemini_blocked_until = None
        log.info("Gemini-Sperre aufgehoben.")
        return False
    return True

async def check_gemini_version(channel):
    """Fragt Gemini ob die aktuelle Version noch empfehlenswert ist. Wird bei neuen Rennkaesten aufgerufen."""

    prompt = (
        f"Wie ist der aktuelle Deprecation-Status fuer {GEMINI_MODEL} und gibt es fuer das Auslesen "
        f"von Screenshots bereits eine stabilere oder neuere Empfehlung? "
        f"Ohne Begruendung, antworte nur mit einem der beiden Saetze: "
        f"'Bleib bei der aktuellen Version.' oder "
        f"'Pruefe, ob ein Update auf Version [Versionsname] sinnvoll ist.'"
    )
    try:
        response = gemini_model.generate_content(prompt, generation_config=GENERATION_CONFIG)
        text = response.text.strip()
        log.info(f"Gemini-Versions-Check: {text}")

        # Nur posten wenn eine neuere Version empfohlen wird
        lower = text.lower()
        if any(kw in lower for kw in ["neuere", "empfehle", "besser", "ersetzen", "wechseln", "aktueller"]):
            embed = discord.Embed(
                title="Gemini Versions-Hinweis",
                description=text,
                color=0xf0a500
            )
            await channel.send(embed=embed)
            log.info("Gemini-Versions-Hinweis im Channel gepostet.")
        else:
            log.info("Gemini-Version ist noch aktuell, kein Hinweis noetig.")
    except Exception as e:
        log.warning(f"Gemini-Versions-Check fehlgeschlagen: {e}")

def analyse_image(image_path):
    img    = Image.open(image_path)
    prompt = build_extract_prompt()
    data   = call_gemini(img, prompt)
    log.info(f"Durchlauf 1: Rennen {data.get('rennen')}, Grid {data.get('grid')}, "
             f"{len(data.get('fahrer', []))} Fahrer")

    if GEMINI_2ND_RUN == 0:
        return data

    run_second = GEMINI_2ND_RUN == 2
    if GEMINI_2ND_RUN == 1:
        run_second = len(validate_deltas(data.get("fahrer", []))) > 0

    if run_second:
        log.info("Starte Durchlauf 2 (Verifikation)...")
        data2 = call_gemini(img, PROMPT_VERIFY_TEMPLATE.format(
            extracted=json.dumps(data, ensure_ascii=False, indent=2)
        ))
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
    Schreibt Ergebnisse ins Sheet via Batch-Update.
    Gibt (warnings, rennen, grid_label, first_pos) zurueck.
    """
    rennen      = int(data["rennen"])
    grid_label  = str(data["grid"]).strip()
    fahrer_list = data["fahrer"]
    warnings    = []

    driver_map = load_driver_list()

    block = resolve_block(sheet, rennen, grid_label)
    log.info(f"Rennen {rennen}, Grid '{grid_label}' -> Block {block}")

    delta_errors       = validate_deltas(fahrer_list)
    fastest_time_int   = None
    fastest_lap_driver = None
    batch              = {}
    red_cells          = []
    first_pos          = None

    # Grid-Label
    r, c = get_grid_label_cell(rennen, block)
    batch[rowcol_to_a1(r, c)] = grid_label

    for fahrer in sorted(fahrer_list, key=lambda x: x["position"]):
        pos            = int(fahrer["position"])
        name_raw       = fahrer["name"]
        auto           = fahrer["auto"]
        auto_unbekannt = fahrer.get("auto_unbekannt", False)
        zeit           = fahrer.get("zeit", "")
        beste_runde    = fahrer.get("beste_runde", "")

        if first_pos is None:
            first_pos = pos

        # Fahrername und Team aus Fahrerliste (case-insensitive)
        name_key = name_raw.lower()
        if name_key in driver_map:
            name, team = driver_map[name_key]
        else:
            name = name_raw
            team = ""
            r_drv, c_drv = get_cell(rennen, block, pos, "driver")
            red_cells.append((r_drv, c_drv))
            warnings.append(
                f"Rennen {rennen}, Grid {grid_label}, Pos {pos}, {name_raw}: "
                f"Fahrer nicht in Fahrerliste"
            )

        racetime, laps = clean_time(zeit)

        log.info(f"  P{pos} {name} | {auto} | racetime={racetime} "
                 f"laps={laps} fl={beste_runde}")

        r_ps,  c_ps  = get_cell(rennen, block, pos, "position")
        r_drv, c_drv = get_cell(rennen, block, pos, "driver")
        r_tm,  c_tm  = get_cell(rennen, block, pos, "team")
        r_car, c_car = get_cell(rennen, block, pos, "car")
        r_rt,  c_rt  = get_cell(rennen, block, pos, "racetime")
        r_lp,  c_lp  = get_cell(rennen, block, pos, "laps")

        batch[rowcol_to_a1(r_ps,  c_ps)]  = pos
        batch[rowcol_to_a1(r_drv, c_drv)] = name
        batch[rowcol_to_a1(r_tm,  c_tm)]  = team
        batch[rowcol_to_a1(r_car, c_car)] = auto
        batch[rowcol_to_a1(r_rt,  c_rt)]  = racetime if racetime is not None else ""
        batch[rowcol_to_a1(r_lp,  c_lp)]  = laps     if laps     is not None else ""

        if auto_unbekannt:
            red_cells.append((r_car, c_car))
            warnings.append(
                f"Rennen {rennen}, Grid {grid_label}, Pos {pos}, {name}: "
                f"Auto '{auto}' nicht erkannt - bitte manuell pruefen"
            )

        if pos in delta_errors:
            red_cells.append((r_rt, c_rt))
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

    sheet.batch_update([
        {"range": addr, "values": [[val]]}
        for addr, val in batch.items()
    ])
    log.info(f"Batch-Update: {len(batch)} Zellen geschrieben")

    for (row, col) in red_cells:
        mark_cell_red(sheet, row, col)

    if fastest_lap_driver and fastest_time_int is not None:
        update_fastest_lap(sheet, rennen, fastest_lap_driver, fastest_time_int)

    return warnings, rennen, grid_label, first_pos

# ── Race-Kasten (Embed) ───────────────────────────────────────────────────────
NA_PHRASES = {"strecke in db_tech definieren!", "n/a", ""}

def build_race_embed(rennen):
    """Liest Daten aus Sheet und baut Discord-Embed fuer Rennkasten."""
    try:
        sheet = get_sheet()
        cs    = col_start(rennen)

        date_raw  = (sheet.cell(3, cs + 3).value or "").strip()  # D3
        track_raw = (sheet.cell(3, cs + 4).value or "").strip()  # E3
        drv_raw   = (sheet.cell(4, cs).value     or "").strip()  # B4

        date_str  = "n/a" if date_raw.lower()  in NA_PHRASES else date_raw
        track_str = "n/a" if track_raw.lower() in NA_PHRASES else track_raw

        lines = [f"**Race {rennen:02d}**"]
        if date_str:
            lines.append(date_str)
        if track_str:
            lines.append(f"**{track_str}**")
        if drv_raw:
            lines.append(f"Drivers: {drv_raw}")

        # Sieger je Grid-Block
        winners = []
        for block in range(4):
            gl_r, gl_c = get_grid_label_cell(rennen, block)
            gl_val     = (sheet.cell(gl_r, gl_c).value or "").strip()
            if not gl_val:
                continue
            win_r, win_c = get_cell(rennen, block, 1, "driver")
            win_name     = (sheet.cell(win_r, win_c).value or "").strip()
            if win_name:
                winners.append(f"Grid {gl_val}: {win_name}")

        if winners:
            lines.append("WINNERS")
            lines.extend(winners)

        # Schnellste Runde
        fl_drv = (sheet.cell(FASTEST_LAP_ROW, cs + REL["fl_driver"]).value or "").strip()
        fl_tim = (sheet.cell(FASTEST_LAP_ROW, cs + REL["fl_time"]).value   or "").strip()
        if fl_drv:
            lines.append(f"FL: {fl_drv} {fl_tim}")

        embed = discord.Embed(
            description="\n".join(lines),
            color=0x1a1a2e
        )
        return embed

    except Exception as e:
        log.error(f"Fehler beim Erstellen des Race-Embeds fuer Rennen {rennen}: {e}")
        embed = discord.Embed(
            description=f"**Race {rennen:02d}**",
            color=0x1a1a2e
        )
        return embed

def parse_race_number_from_embed(message):
    """Liest Rennnummer aus Bot-Embed-Description (**Race XX**). Gibt None zurueck wenn kein Race-Embed."""
    if not hasattr(discord_client, 'user') or discord_client.user is None:
        return None
    if message.author.id != discord_client.user.id:
        return None
    for embed in message.embeds:
        if embed.description:
            # Race-Kasten: beginnt mit **Race XX**, kein · im Text (Screenshot-Posts haben ·)
            m = re.match(r"^\*\*Race (\d+)\*\*", embed.description.strip())
            if m and "·" not in embed.description:
                return int(m.group(1))
    return None

def parse_screenshot_meta_from_embed(message):
    """Liest race/grid/page aus Screenshot-Description: 'Race 03 · Grid 2a · Seite 1'"""
    if not hasattr(discord_client, 'user') or discord_client.user is None:
        return None
    if message.author.id != discord_client.user.id:
        return None
    for embed in message.embeds:
        if embed.description:
            m = re.match(r"Race (\d+)\s+\S+\s+Grid (\S+)\s+\S+\s+Seite (\d+)", embed.description.strip())
            if m:
                return {
                    "race": int(m.group(1)),
                    "grid": m.group(2),
                    "page": int(m.group(3)),
                }
    return None

GRID_ORDER = {"1": 0, "2": 1, "2a": 1, "2b": 2, "3": 3}

def screenshot_sort_key(meta):
    if meta is None:
        return (999, 999, 999)
    grid_idx = GRID_ORDER.get(meta["grid"].lower(), 99)
    return (meta["race"], grid_idx, meta["page"])

# ── Discord Hilfsfunktionen ───────────────────────────────────────────────────
async def find_last_race_box(channel):
    """Findet die letzte Race-Kasten-Nachricht. Gibt (message, rennen) zurueck."""
    async for msg in channel.history(limit=200):
        rn = parse_race_number_from_embed(msg)
        if rn is not None:
            return msg, rn
    return None, None

async def find_race_box(channel, rennen):
    """Findet Race-Kasten fuer ein bestimmtes Rennen."""
    async for msg in channel.history(limit=200):
        rn = parse_race_number_from_embed(msg)
        if rn == rennen:
            return msg
    return None

async def update_race_box(channel, rennen):
    """Aktualisiert Race-Kasten (oder erstellt neuen falls nicht vorhanden)."""
    embed    = build_race_embed(rennen)
    existing = await find_race_box(channel, rennen)
    if existing:
        await existing.edit(embed=embed)
        log.info(f"Race-Kasten Rennen {rennen} aktualisiert.")
    else:
        await channel.send(embed=embed)
        log.info(f"Race-Kasten Rennen {rennen} erstellt.")

# ── !sort ─────────────────────────────────────────────────────────────────────
async def cmd_sort(channel):
    """Sortiert Bot-Screenshot-Posts nach Race/Grid/Seite seit dem letzten Rennkasten."""
    last_box_msg, _ = await find_last_race_box(channel)

    screenshots = []
    async for msg in channel.history(limit=200, after=last_box_msg):
        if msg.author.id != discord_client.user.id:
            continue
        meta = parse_screenshot_meta_from_embed(msg)
        if meta is None:
            continue
        imgs = [a for a in msg.attachments
                if a.content_type and a.content_type.startswith("image/")]
        if not imgs:
            continue
        screenshots.append((msg, meta, imgs[0]))

    if not screenshots:
        log.info("!sort: Keine Bot-Screenshots gefunden.")
        return

    screenshots.sort(key=lambda x: screenshot_sort_key(x[1]))

    for msg, meta, img_att in screenshots:
        img_data = requests.get(img_att.url).content
        with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
            tmp_path = f.name
        try:
            with open(tmp_path, "wb") as f:
                f.write(img_data)
            grid_str = meta["grid"].upper() if meta["grid"].isdigit() else meta["grid"]
            title    = f"Race {meta['race']:02d} \u00b7 Grid {grid_str} \u00b7 Seite {meta['page']}"
            embed    = discord.Embed(description=title, color=0x2b2d31)
            with open(tmp_path, "rb") as f:
                await channel.send(
                    file=discord.File(f, filename="screenshot.png"),
                    embed=embed
                )
            await msg.delete()
        finally:
            os.unlink(tmp_path)
        await asyncio.sleep(1)

    log.info(f"!sort: {len(screenshots)} Screenshots neu sortiert.")

# ── Reaktions-Hilfsfunktionen ─────────────────────────────────────────────────
async def already_processed(message):
    try:
        fresh = await message.channel.fetch_message(message.id)
    except Exception:
        return True
    for reaction in fresh.reactions:
        if str(reaction.emoji) in (DONE_EMOJI, ERROR_EMOJI):
            async for user in reaction.users():
                if user.id == discord_client.user.id:
                    return True
    return False

async def get_processed_count(message):
    fresh = await message.channel.fetch_message(message.id)
    for reaction in fresh.reactions:
        emoji_str = str(reaction.emoji)
        if emoji_str in NUMBER_EMOJIS:
            async for user in reaction.users():
                if user.id == discord_client.user.id:
                    return NUMBER_EMOJIS.index(emoji_str) + 1
    return 0

async def remove_number_reactions(message):
    fresh     = await message.channel.fetch_message(message.id)
    to_remove = []
    for reaction in fresh.reactions:
        if str(reaction.emoji) in NUMBER_EMOJIS:
            async for user in reaction.users():
                if user.id == discord_client.user.id:
                    to_remove.append(reaction.emoji)
    for emoji in to_remove:
        try:
            await message.remove_reaction(emoji, discord_client.user)
        except Exception as e:
            log.warning(f"Konnte Reaktion {emoji} nicht entfernen: {e}")

# ── Screenshot verarbeiten und reposten ──────────────────────────────────────
async def process_image(message, attachment):
    """
    Verarbeitet ein Bild, postet es als Bot-Post und aktualisiert den Race-Kasten.
    Gibt (elapsed, success) zurueck.
    """
    log.info(f"Verarbeite: {attachment.filename} von {message.author}")
    channel = message.channel
    started = asyncio.get_event_loop().time()
    success = False
    elapsed = 0

    with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
        tmp_path = f.name

    try:
        img_data = requests.get(attachment.url).content
        with open(tmp_path, "wb") as f:
            f.write(img_data)

        data  = analyse_image(tmp_path)
        sheet = get_sheet()
        warnings, rennen, grid_label, first_pos = write_results(sheet, data)

        # Seite bestimmen: P1 = Seite 1, sonst Seite 2
        page = 1 if (first_pos is None or first_pos == 1) else 2

        for w in warnings:
            await channel.send(w)

        # Screenshot als Bot-Post mit lesbarem Embed
        grid_str = grid_label.upper() if grid_label.isdigit() else grid_label
        title    = f"Race {rennen:02d} \u00b7 Grid {grid_str} \u00b7 Seite {page}"
        embed    = discord.Embed(description=title, color=0x2b2d31)

        # Duplikat-Check: existiert bereits ein Bot-Post mit gleichen Metadaten?
        async for old_msg in channel.history(limit=100):
            old_meta = parse_screenshot_meta_from_embed(old_msg)
            if (old_meta and old_meta["race"] == rennen
                    and old_meta["grid"] == grid_label
                    and old_meta["page"] == page):
                try:
                    await old_msg.delete()
                    log.info(f"Duplikat-Post geloescht: Race {rennen}, Grid {grid_label}, Seite {page}")
                except Exception as e:
                    log.warning(f"Konnte Duplikat nicht loeschen: {e}")
                break

        with open(tmp_path, "rb") as f:
            await channel.send(
                file=discord.File(f, filename="screenshot.png"),
                embed=embed
            )

        # Race-Kasten aktualisieren
        await update_race_box(channel, rennen)

        elapsed = asyncio.get_event_loop().time() - started
        log.info(f"Verarbeitet in {elapsed:.1f}s. {len(warnings)} Warnung(en).")
        success = True

    except GeminiQuotaError:
        await channel.send(
            f"Gemini-Tageskontingent erschoepft. Auswertung pausiert fuer ca. "
            f"{GEMINI_BACKOFF_MINUTES} Minuten. Bild wird automatisch verarbeitet."
        )
        log.warning("Quota-Fehler, kein Emoji gesetzt.")
        success = None

    except Exception as e:
        log.error(f"Fehler: {e}", exc_info=True)
        await channel.send(f"Fehler: {type(e).__name__}: {str(e)[:200]}")
        success = False

    finally:
        elapsed = asyncio.get_event_loop().time() - started
        os.unlink(tmp_path)

    return elapsed, success

# ── Befehls-Handler ───────────────────────────────────────────────────────────
async def handle_command(message):
    """Verarbeitet Bot-Befehle. Loescht den User-Post danach."""
    channel = message.channel
    content = message.content.strip()
    parts   = content.split()
    cmd     = parts[0].lower()

    try:
        if cmd == "!next":
            _, last_rn = await find_last_race_box(channel)
            next_rn    = (last_rn + 1) if last_rn else 1
            if next_rn > 1:
                await cmd_sort(channel)
            embed = discord.Embed(
                description=f"**Race {next_rn:02d}**",
                color=0x1a1a2e
            )
            await channel.send(embed=embed)
            log.info(f"!next: Race-Kasten fuer Rennen {next_rn} erstellt.")
            await check_gemini_version(channel)

        elif cmd == "!race":
            if len(parts) < 2:
                await channel.send("Verwendung: !race <Nummer>")
                return
            rn = int(parts[1])
            if rn > 1:
                await cmd_sort(channel)
            embed = discord.Embed(
                description=f"**Race {rn:02d}**",
                color=0x1a1a2e
            )
            await channel.send(embed=embed)
            log.info(f"!race: Race-Kasten fuer Rennen {rn} erstellt.")
            await check_gemini_version(channel)

        elif cmd == "!update":
            load_car_list()
            if len(parts) >= 2:
                rn = int(parts[1])
                await update_race_box(channel, rn)
                await channel.send(
                    f"Fahrzeugliste aktualisiert. Race-Kasten {rn:02d} aktualisiert.",
                    delete_after=10
                )
            else:
                await channel.send("Fahrzeugliste aktualisiert.", delete_after=10)

        elif cmd == "!sort":
            await cmd_sort(channel)
            await channel.send("Screenshots sortiert.", delete_after=5)

        elif cmd == "!clean":
            deleted = 0
            async for msg in channel.history(limit=200):
                if msg.author.id != discord_client.user.id:
                    continue
                has_embed = len(msg.embeds) > 0
                has_image = any(
                    a.content_type and a.content_type.startswith("image/")
                    for a in msg.attachments
                )
                if not has_embed and not has_image:
                    await msg.delete()
                    deleted += 1
                    await asyncio.sleep(0.5)
            log.info(f"!clean: {deleted} Nachrichten geloescht.")

        else:
            return

    except Exception as e:
        log.error(f"Fehler bei Befehl '{cmd}': {e}", exc_info=True)
        await channel.send(f"Fehler bei {cmd}: {str(e)[:200]}")
    finally:
        try:
            await message.delete()
        except Exception:
            pass

# ── Discord Bot ───────────────────────────────────────────────────────────────
intents = discord.Intents.default()
intents.message_content = True
intents.reactions       = True

discord_client = discord.Client(intents=intents)

async def scan_channel():
    await discord_client.wait_until_ready()
    channel = discord_client.get_channel(DISCORD_CHANNEL_ID)

    if channel is None:
        log.error(f"Channel {DISCORD_CHANNEL_ID} nicht gefunden!")
        return

    log.info(f"Scanne #{channel.name} alle {POLL_INTERVAL}s | GEMINI_2ND_RUN={GEMINI_2ND_RUN}")

    # Beim Start: Race 01 erstellen falls noch kein Rennkasten vorhanden
    _, existing_rn = await find_last_race_box(channel)
    if existing_rn is None:
        embed = discord.Embed(description="**Race 01**", color=0x1a1a2e)
        await channel.send(embed=embed)
        log.info("Erster Race-Kasten (Race 01) erstellt.")
        await check_gemini_version(channel)

    while not discord_client.is_closed():
        try:
            if gemini_is_blocked():
                mins = int((gemini_blocked_until - datetime.now()).total_seconds() / 60)
                log.info(f"Gemini gesperrt, ueberspringe Scan. Noch ca. {mins} Minuten.")
                await asyncio.sleep(POLL_INTERVAL)
                continue

            async for message in channel.history(limit=50):

                # Befehle verarbeiten (nur von Nicht-Bot-Usern)
                if (message.content.startswith("!")
                        and message.author.id != discord_client.user.id):
                    await handle_command(message)
                    continue

                # Nur fremde Posts mit Bildern auslesen
                if message.author.id == discord_client.user.id:
                    continue

                attachments = [
                    a for a in message.attachments
                    if a.content_type and a.content_type.startswith("image/")
                ]
                if not attachments:
                    continue
                if await already_processed(message):
                    continue

                try:
                    processed_count = await get_processed_count(message)
                except Exception as e:
                    log.warning(f"Reaktionen nicht lesbar, ueberspringe: {e}")
                    continue

                total      = len(attachments)
                next_index = processed_count
                if next_index >= total:
                    continue

                attachment      = attachments[next_index]
                elapsed, success = await process_image(message, attachment)

                if gemini_is_blocked():
                    break

                if success is True:
                    new_count = processed_count + 1
                    await remove_number_reactions(message)
                    if new_count >= total:
                        # Alle Bilder fertig: Original-Post loeschen
                        try:
                            await message.delete()
                            log.info("Original-Post geloescht.")
                        except Exception as e:
                            log.warning(f"Konnte Original-Post nicht loeschen: {e}")
                    else:
                        await message.add_reaction(NUMBER_EMOJIS[new_count - 1])
                        log.info(f"Bild {new_count}/{total} verarbeitet.")
                elif success is False:
                    await remove_number_reactions(message)
                    await message.add_reaction(ERROR_EMOJI)
                # success is None -> Quota, kein Emoji

                remaining = POLL_INTERVAL - elapsed
                if remaining > 0:
                    log.info(f"Warte {remaining:.1f}s")
                    await asyncio.sleep(remaining)

        except Exception as e:
            log.error(f"Scan-Fehler: {e}", exc_info=True)

        await asyncio.sleep(POLL_INTERVAL)

# ── Webserver (Render keep-alive) ─────────────────────────────────────────────
from aiohttp import web

async def handle(request):
    return web.Response(text="OK")

async def start_webserver():
    app    = web.Application()
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
    load_car_list()
    if not car_list:
        channel = discord_client.get_channel(DISCORD_CHANNEL_ID)
        if channel:
            await channel.send(
                "⚠️ Fahrzeugliste konnte nicht geladen werden (DB_Tech, Spalte R ab Zeile 8). "
                "Fahrzeugnamen werden nicht uebersetzt. Bitte !update ausfuehren nach Pruefung."
            )
    discord_client.loop.create_task(scan_channel())

async def main():
    await start_webserver()
    await discord_client.start(DISCORD_TOKEN)

if __name__ == "__main__":
    asyncio.run(main())

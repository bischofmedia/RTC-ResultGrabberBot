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

# Uebersetzungstabelle: {spielname_lower: tabellenname}
# Spielname = Spalte B, Tabellenname = Spalte A in Car_Translate
car_translate_map: dict = {}

class GeminiQuotaError(Exception):
    pass

# Nachrichten-IDs die gerade verarbeitet werden (verhindert Doppel-Scan)
processing_ids: set = set()

# Aktuelle Quota-Warn-Nachricht (wird geupdated statt neu gepostet)
quota_msg = None

# Grid-Farb-Emojis und Seite-Emojis
GRID_EMOJI = {
    "1":  "🟡",  # 🟡 gelb
    "2":  "🔵",  # 🔵 blau
    "2a": "🔵",  # 🔵 blau
    "2b": "🔴",  # 🔴 rot
    "3":  "🟢",  # 🟢 gruen
}
PAGE_EMOJI = {
    1: "🔼",  # 🔼 Seite 1
    2: "🔽",  # 🔽 Seite 2
}
ALL_GRID_EMOJIS = set(GRID_EMOJI.values())
ALL_PAGE_EMOJIS = set(PAGE_EMOJI.values())
ALL_MARKER_EMOJIS = ALL_GRID_EMOJIS | ALL_PAGE_EMOJIS

def get_marker_emojis(grid_label, page):
    """Gibt (grid_emoji, page_emoji) fuer ein Grid/Seite-Paar zurueck."""
    g = GRID_EMOJI.get(grid_label.lower(), "❓")  # ❓ wenn unbekannt
    p = PAGE_EMOJI.get(page, "❓")
    return g, p

def parse_meta_from_reactions(reactions, bot_id):
    """Liest Grid und Seite aus Reaktionen eines Bot-Bild-Posts.
    Gibt {"grid": str, "page": int} oder None zurueck."""
    found_grid = None
    found_page = None
    for reaction in reactions:
        emoji_str = str(reaction.emoji)
        # Synchron pruefen ob Bot reagiert hat - reactions.users() ist async,
        # daher pruefen wir einfach ob reaction.me True ist
        if not reaction.me:
            continue
        for gl, ge in GRID_EMOJI.items():
            if emoji_str == ge and found_grid is None:
                found_grid = gl
        for pg, pe in PAGE_EMOJI.items():
            if emoji_str == pe:
                found_page = pg
    if found_grid is not None and found_page is not None:
        return {"grid": found_grid, "page": found_page}
    return None

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
    """Laedt Fahrzeugliste aus DB_tech und Uebersetzungstabelle aus Car_Translate."""
    global car_list, car_translate_map
    try:
        wb    = get_workbook()
        sheet = wb.worksheet("DB_tech")
        vals  = sheet.get("R8:R300")
        car_list = [row[0].strip() for row in vals if row and row[0].strip()]
        if not car_list:
            log.warning("Fahrzeugliste ist leer! Bitte DB_tech pruefen (Spalte R ab Zeile 8).")
        else:
            log.info(f"Fahrzeugliste geladen: {len(car_list)} Eintraege")
    except Exception as e:
        log.error(f"KRITISCH: Fahrzeugliste konnte nicht geladen werden: {e}")
        car_list = []

    # Car_Translate laden: Spalte A = Tabellenname, Spalte B = Spielname
    try:
        wb    = get_workbook()
        sheet = wb.worksheet("Car_Translate")
        rows  = sheet.get("A2:B1000")  # Zeile 1 = Ueberschrift
        car_translate_map = {}
        for row in rows:
            tabellenname = row[0].strip() if len(row) > 0 else ""
            spielname    = row[1].strip() if len(row) > 1 else ""
            if tabellenname and spielname:
                car_translate_map[spielname.lower()] = tabellenname
        log.info(f"Car_Translate geladen: {len(car_translate_map)} Eintraege")
    except Exception as e:
        log.warning(f"Car_Translate nicht geladen (noch nicht angelegt?): {e}")
        car_translate_map = {}

def load_driver_list():
    """Laedt Fahrerliste aus DB_drvr.
    Spalte C = Tabellenname, Spalte K = Team, Spalte DB = GT7-Spielname.
    Gibt zwei Dicts zurueck:
      driver_map:    {lower_tabellenname: (tabellenname, team)}
      gt7_name_map:  {lower_gt7name:      (tabellenname, team)}
    """
    try:
        wb    = get_workbook()
        sheet = wb.worksheet("DB_drvr")

        # Spalte C+K: Tabellenname und Team
        rows_ck  = sheet.get("C5:K200")
        # Spalte DB: GT7-Spielnamen (separate Abfrage)
        rows_db  = sheet.get("DB5:DB200")

        driver_map   = {}
        gt7_name_map = {}

        for i, row in enumerate(rows_ck):
            name = row[0].strip() if len(row) > 0 else ""
            team = row[8].strip() if len(row) > 8 else ""
            if name:
                driver_map[name.lower()] = (name, team)
            # GT7-Name aus Spalte DB, gleiche Zeile
            gt7_row  = rows_db[i] if i < len(rows_db) else []
            gt7_name = gt7_row[0].strip() if gt7_row else ""
            if gt7_name and name:
                gt7_name_map[gt7_name.lower()] = (name, team)

        if not driver_map:
            log.warning("Fahrerliste ist leer! Bitte DB_drvr pruefen (Spalte C ab Zeile 5).")
        else:
            log.info(f"Fahrerliste geladen: {len(driver_map)} Eintraege, "
                     f"{len(gt7_name_map)} GT7-Namen")
        return driver_map, gt7_name_map
    except Exception as e:
        log.error(f"KRITISCH: Fahrerliste konnte nicht geladen werden: {e}")
        return {}, {}

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

GREY2 = {"red": 0.8, "green": 0.8, "blue": 0.8}  # Hellgrau 2 in Google Sheets
RED   = {"red": 1.0, "green": 0.0, "blue": 0.0}

def batch_format_cells(sheet, grey_cells, red_cells):
    """Formatiert alle Zellen in einem einzigen API-Aufruf statt einzeln."""
    formats = []
    for (row, col) in grey_cells:
        formats.append({
            "range": rowcol_to_a1(row, col),
            "format": {"textFormat": {"foregroundColor": GREY2}}
        })
    for (row, col) in red_cells:
        formats.append({
            "range": rowcol_to_a1(row, col),
            "format": {"textFormat": {"foregroundColor": RED}}
        })
    if formats:
        sheet.batch_format(formats)

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
    """Erstellt den Extraktions-Prompt. Fahrzeugname wird exakt aus Bild gelesen."""
    return (
        "Analysiere diesen Gran Turismo Ergebnisscreen und extrahiere die Daten als JSON.\n\n"
        "Gib NUR gueltiges JSON zurueck, kein Markdown, keine Erklaerungen.\n\n"
        "FAHRERNAMEN: Kopiere exakt so wie im Bild. Keine Korrekturen.\n"
        "Beispiel: 'Bismark' bleibt 'Bismark', 'XxChillerHDxX95' bleibt exakt so.\n\n"
        "FAHRZEUGNAMEN: Lies den Namen exakt so wie er im Bild steht.\n"
        "Kopiere unveraendert, inklusive Jahreszahl, Sonderzeichen und Klammern.\n\n"
        "Format:\n"
        "{\n"
        '  "rennen": <Zahl>,\n'
        '  "grid": "<1, 2, 2a, 2b oder 3>",\n'
        '  "fahrer": [\n'
        "    {\n"
        '      "position": <Zahl>,\n'
        '      "name": "<exakt wie im Bild>",\n'
        '      "auto": "<exakt wie im Bild>",\n'
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
        err_str = str(e).lower()
        if "per day" in err_str or "daily" in err_str or "quota_exceeded" in err_str:
            # Tageslimit: bis 09:00 Uhr lokaler Zeit (Google Reset = 0 Uhr Pacific = 9 Uhr DE)
            now  = datetime.now()
            reset = now.replace(hour=9, minute=0, second=0, microsecond=0)
            if now >= reset:
                reset += timedelta(days=1)
            gemini_blocked_until = reset
            log.error(f"Gemini Tageslimit erreicht. Sperre bis {reset.strftime('%H:%M')} Uhr.")
            raise GeminiQuotaError("daily") from e
        else:
            # Minutenlimit: kurze Pause
            gemini_blocked_until = datetime.now() + timedelta(minutes=5)
            log.warning("Gemini Minutenlimit erreicht. Sperre fuer 5 Minuten.")
            raise GeminiQuotaError("rpm") from e
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

def berlin_time_str(dt):
    """Gibt Uhrzeit in Berliner Zeit als HH:MM zurueck."""
    try:
        import zoneinfo
        berlin = zoneinfo.ZoneInfo("Europe/Berlin")
        dt_berlin = dt.astimezone(berlin)
    except Exception:
        # Fallback: UTC+1/+2 je nach Jahreszeit
        dt_berlin = dt + timedelta(hours=2)
    return dt_berlin.strftime("%H:%M")

async def clear_quota_msg(channel):
    """Loescht die Quota-Warnmeldung wenn Sperre aufgehoben."""
    global quota_msg
    if quota_msg:
        try:
            await quota_msg.delete()
        except Exception:
            pass
        quota_msg = None

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
def write_results(sheet, data, rennen_override=None):
    """
    Schreibt Ergebnisse ins Sheet via Batch-Update.
    Gibt (warnings, rennen, grid_label, first_pos) zurueck.
    rennen_override: wenn gesetzt, wird dieser Wert statt data["rennen"] verwendet.
    """
    rennen_aus_screenshot = int(data.get("rennen", 0))
    rennen      = rennen_override if rennen_override is not None else rennen_aus_screenshot
    grid_label  = str(data["grid"]).strip()
    fahrer_list = data["fahrer"]
    warnings    = []

    driver_map, gt7_name_map = load_driver_list()

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
        auto_raw       = fahrer["auto"]
        # Uebersetzung: Spielname -> Tabellenname via Car_Translate
        auto           = car_translate_map.get(auto_raw.lower(), auto_raw)
        auto_unbekannt = auto == auto_raw and auto_raw.lower() not in car_translate_map
        zeit           = fahrer.get("zeit", "")
        beste_runde    = fahrer.get("beste_runde", "")

        if first_pos is None:
            first_pos = pos

        # Fahrername und Team aus Fahrerliste (case-insensitive)
        # Erst Tabellenname (Spalte C), dann GT7-Name (Spalte DB)
        name_key = name_raw.lower()
        if name_key in driver_map:
            name, team = driver_map[name_key]
        elif name_key in gt7_name_map:
            name, team = gt7_name_map[name_key]
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

        r_drv, c_drv = get_cell(rennen, block, pos, "driver")
        r_tm,  c_tm  = get_cell(rennen, block, pos, "team")
        r_car, c_car = get_cell(rennen, block, pos, "car")
        r_rt,  c_rt  = get_cell(rennen, block, pos, "racetime")
        r_lp,  c_lp  = get_cell(rennen, block, pos, "laps")

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

    # Alle beschriebenen Zellen grau, Fehler-Zellen rot – ein einziger API-Aufruf
    all_cells = set()
    for fahrer in fahrer_list:
        pos = int(fahrer["position"])
        for field in ("driver", "team", "car", "racetime", "laps"):
            all_cells.add(get_cell(rennen, block, pos, field))
    gl_r, gl_c = get_grid_label_cell(rennen, block)
    all_cells.add((gl_r, gl_c))

    red_set  = set(red_cells)
    grey_set = all_cells - red_set
    batch_format_cells(sheet, grey_set, red_set)

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

        date_raw  = (sheet.cell(3, cs + 2).value or "").strip()  # D3
        track_raw = (sheet.cell(3, cs + 3).value or "").strip()  # E3
        drv_raw   = (sheet.cell(4, cs).value     or "").strip()  # B4

        date_str  = "n/a" if date_raw.lower()  in NA_PHRASES else date_raw
        track_str = "n/a" if track_raw.lower() in NA_PHRASES else track_raw

        # Erste Zeile: Race XX - Track (fett)
        if track_str and track_str != "n/a":
            lines = [f"**Race {rennen:02d} - {track_str}**"]
        else:
            lines = [f"**Race {rennen:02d}**"]

        if date_str and date_str != "n/a":
            lines.append(date_str)
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
            lines.append("")
            lines.append("**Sieger der Grids 🏆**")
            lines.extend(winners)

        # Schnellste Runde: erst Zeit, dann Name
        fl_drv = (sheet.cell(FASTEST_LAP_ROW, cs + REL["fl_driver"]).value or "").strip()
        fl_tim = (sheet.cell(FASTEST_LAP_ROW, cs + REL["fl_time"]).value   or "").strip()
        if fl_drv:
            lines.append(f"FL: {fl_tim} - {fl_drv}")

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
            m = re.match(r"^\*\*Race (\d+)", embed.description.strip())
            if m and "·" not in embed.description:
                return int(m.group(1))
    return None

def parse_screenshot_meta_from_msg(message):
    """Liest Grid und Seite aus Reaktions-Emojis eines Bot-Bild-Posts.
    Gibt {"grid": str, "page": int} oder None zurueck."""
    if not hasattr(discord_client, 'user') or discord_client.user is None:
        return None
    if message.author.id != discord_client.user.id:
        return None
    # Nur Posts mit Bild-Anhang
    has_image = any(a.content_type and a.content_type.startswith("image/")
                    for a in message.attachments)
    if not has_image:
        return None
    return parse_meta_from_reactions(message.reactions, discord_client.user.id)

GRID_ORDER = {"1": 0, "2": 1, "2a": 1, "2b": 2, "3": 3}

def screenshot_sort_key(meta):
    if meta is None:
        return (999, 999)
    grid_idx = GRID_ORDER.get(meta["grid"].lower(), 99)
    return (grid_idx, meta["page"])

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
def build_legend_embed(downloaded):
    """Baut Legende-Embed aus den tatsaechlich vorhandenen Grids."""
    grids_present = set(meta["grid"].lower() for _, meta, _ in downloaded)

    grid_line = []
    if "1" in grids_present:
        grid_line.append(f"🟡 Grid 1")
    has_2b = "2b" in grids_present
    if "2" in grids_present or "2a" in grids_present:
        label = "Grid 2a" if has_2b else "Grid 2"
        grid_line.append(f"🔵 {label}")
    if has_2b:
        grid_line.append(f"🔴 Grid 2b")
    if "3" in grids_present:
        grid_line.append(f"🟢 Grid 3")

    line1 = "  ".join(grid_line)
    line2 = "🔼 Seite 1    🔽 Seite 2"

    embed = discord.Embed(
        description=f"-# {line1}\n-# {line2}",
        color=0x2b2d31
    )
    embed.set_footer(text="​")  # Unsichtbares Zeichen als Marker
    return embed

def is_legend_embed(message):
    """Prueft ob eine Nachricht die Legende ist."""
    if not hasattr(discord_client, "user") or discord_client.user is None:
        return False
    if message.author.id != discord_client.user.id:
        return False
    for embed in message.embeds:
        if embed.footer and embed.footer.text == "​":
            return True
    return False


async def cmd_check(channel):
    """
    !check - Liest alle Fahrer- und Auto-Eintraege des aktuellen Rennens,
    prueft jeden gegen die Uebersetzungstabellen und korrigiert wo moeglich.
    Gibt eine Liste aller Abweichungen aus.
    """
    status = await channel.send("Prüfe Eintraege...")
    try:
        _, rennen = await find_last_race_box(channel)
        if rennen is None:
            await status.edit(content="Kein Race-Kasten gefunden.")
            return

        sheet    = get_sheet()
        cs       = col_start(rennen)
        row_from = FIRST_DATA_ROW
        row_to   = FIRST_DATA_ROW + 4 * ROW_OFFSET_PER_GRID - 1
        c_drv    = cs + REL["driver"]
        c_car    = cs + REL["car"]

        # Fahrer und Autos in einem Aufruf lesen
        data_range = f"{rowcol_to_a1(row_from, c_drv)}:{rowcol_to_a1(row_to, c_car)}"
        rows = sheet.get(data_range)

        # Immer frisch laden damit neue Eintraege sofort wirken
        load_car_list()
        driver_map, gt7_name_map = load_driver_list()

        batch_vals  = {}
        grey_cells  = []
        report      = []  # [(typ, original, korrigiert_zu, ok)]

        for i, row in enumerate(rows):
            abs_row  = row_from + i
            drv_val  = row[0].strip() if len(row) > 0 else ""
            car_val  = row[REL["car"] - REL["driver"]].strip() if len(row) > (REL["car"] - REL["driver"]) else ""

            # Fahrer pruefen
            if drv_val:
                if drv_val.lower() in driver_map:
                    pass  # bereits korrekter Tabellenname -> ok
                elif drv_val.lower() in gt7_name_map:
                    # GT7-Name gefunden -> in Tabellennamen uebersetzen
                    korrigiert, _ = gt7_name_map[drv_val.lower()]
                    batch_vals[rowcol_to_a1(abs_row, c_drv)] = korrigiert
                    grey_cells.append((abs_row, c_drv))
                    report.append(("Fahrer", drv_val, korrigiert, True))
                else:
                    # Weder Tabellenname noch bekannter GT7-Name
                    report.append(("Fahrer", drv_val, None, False))

            # Auto pruefen
            if car_val:
                valid_tabellen = {c.lower() for c in car_list}
                if car_val.lower() in valid_tabellen:
                    pass  # bereits korrekter Tabellenname -> ok
                elif car_val.lower() in car_translate_map:
                    # Spielname gefunden -> in Tabellenname uebersetzen
                    korrigiert = car_translate_map[car_val.lower()]
                    batch_vals[rowcol_to_a1(abs_row, c_car)] = korrigiert
                    grey_cells.append((abs_row, c_car))
                    report.append(("Auto", car_val, korrigiert, True))
                else:
                    # Weder Tabellenname noch bekannter Spielname
                    report.append(("Auto", car_val, None, False))

        # Korrekturen schreiben
        if batch_vals:
            sheet.batch_update([
                {"range": addr, "values": [[val]]}
                for addr, val in batch_vals.items()
            ])

        # Alle Zellen grau faerben die jetzt korrekt sind
        # (korrigierte + bereits korrekte - beide sollen hellgrau werden)
        valid_tabellen = {c.lower() for c in car_list}
        all_grey = list(grey_cells)  # bereits korrigierte
        for i, row in enumerate(rows):
            abs_row = row_from + i
            car_idx = REL["car"] - REL["driver"]
            drv_val = row[0].strip() if len(row) > 0 else ""
            car_val = row[car_idx].strip() if len(row) > car_idx else ""
            # Endname nach Korrektur bestimmen
            drv_end = next((r[2] for r in report if r[0]=="Fahrer" and r[1]==drv_val and r[3]), drv_val)
            car_end = next((r[2] for r in report if r[0]=="Auto"   and r[1]==car_val and r[3]), car_val)
            if drv_val and drv_end.lower() in driver_map:
                cell = (abs_row, c_drv)
                if cell not in all_grey:
                    all_grey.append(cell)
            if car_val and car_end.lower() in valid_tabellen:
                cell = (abs_row, c_car)
                if cell not in all_grey:
                    all_grey.append(cell)
        if all_grey:
            batch_format_cells(sheet, all_grey, [])

        # Alte Warnmeldungen im Channel loeschen wenn Eintrag jetzt korrekt ist
        corrected_names = {r[1].lower() for r in report if r[3] and r[0] == "Fahrer"}
        corrected_cars  = {r[1].lower() for r in report if r[3] and r[0] == "Auto"}
        last_box_msg, _ = await find_last_race_box(channel)
        async for msg in channel.history(limit=200, after=last_box_msg):
            if msg.author.id != discord_client.user.id or not msg.content:
                continue
            txt_lower = msg.content.lower()
            should_delete = False
            if "fahrer nicht in fahrerliste" in txt_lower:
                if any(name in txt_lower for name in corrected_names):
                    should_delete = True
            if "nicht in fahrzeugliste" in txt_lower:
                if any(car in txt_lower for car in corrected_cars):
                    should_delete = True
            if should_delete:
                try:
                    await msg.delete()
                except Exception:
                    pass

        # Meldung aufbauen
        await status.delete()
        if not report:
            await channel.send("✅ Alle Fahrer und Fahrzeuge korrekt.")
        else:
            lines = [f"**!check Rennen {rennen:02d}**"]
            for typ, original, korrigiert, ok in report:
                if ok:
                    lines.append(f"✅ {typ}: `{original}` → `{korrigiert}`")
                else:
                    lines.append(f"❌ {typ}: `{original}` – nicht in Tabelle")
            await channel.send("\n".join(lines))

        log.info(f"!check: {len([r for r in report if r[3]])} korrigiert, "
                 f"{len([r for r in report if not r[3]])} nicht gefunden.")

    except Exception as e:
        log.error(f"!check Fehler: {e}", exc_info=True)
        await status.edit(content=f"Fehler: {type(e).__name__}: {str(e)[:200]}")


async def update_legend(channel, downloaded):
    """Erstellt oder aktualisiert die Legende nach den Screenshots."""
    embed = build_legend_embed(downloaded)

    # Vorhandene Legende suchen
    last_box_msg, _ = await find_last_race_box(channel)
    existing = None
    async for msg in channel.history(limit=200, after=last_box_msg):
        if is_legend_embed(msg):
            existing = msg
            break

    if existing:
        # Legende ans Ende verschieben: alte loeschen, neue posten
        try:
            await existing.delete()
        except Exception as e:
            log.warning(f"Konnte Legende nicht loeschen: {e}")

    await channel.send(embed=embed)
    log.info("Legende aktualisiert.")


async def cmd_clean(channel):
    """Loescht Bot-Textnachrichten seit dem letzten Race-Kasten.
    Faerbt nur das aktuelle Rennen grau - versiegelte Rennen werden nicht angeruehrt."""
    last_box_msg, aktuelles_rennen = await find_last_race_box(channel)

    # Nur Nachrichten NACH dem letzten Race-Kasten loeschen
    deleted = 0
    async for msg in channel.history(limit=200, after=last_box_msg):
        if msg.author.id != discord_client.user.id:
            continue
        has_embed = len(msg.embeds) > 0
        has_image = any(
            a.content_type and a.content_type.startswith("image/")
            for a in msg.attachments
        )
        if not has_embed and not has_image and not is_legend_embed(msg):
            await msg.delete()
            deleted += 1
            await asyncio.sleep(0.6)
    log.info(f"cmd_clean: {deleted} Nachrichten geloescht.")

    # Nur aktuelles Rennen grau faerben
    if aktuelles_rennen is not None:
        sheet    = get_sheet()
        cs       = col_start(aktuelles_rennen)
        col_from = rowcol_to_a1(FIRST_DATA_ROW, cs + REL["driver"])[:-len(str(FIRST_DATA_ROW))]
        col_to   = rowcol_to_a1(FIRST_DATA_ROW, cs + REL["laps"])[:-len(str(FIRST_DATA_ROW))]
        row_end  = FIRST_DATA_ROW + 4 * ROW_OFFSET_PER_GRID - 1
        rng      = f"{col_from}{FIRST_DATA_ROW}:{col_to}{row_end}"
        sheet.format(rng, {"textFormat": {"foregroundColor": GREY2}})
        log.info(f"cmd_clean: Rennen {aktuelles_rennen} grau gefaerbt.")


async def cmd_sort(channel):
    """
    Sortiert Bot-Screenshot-Posts nach Grid/Seite seit dem letzten Rennkasten.
    Liest Metadaten aus Reaktions-Emojis. Postet Bilder neu, dann Textnachrichten.
    """
    last_box_msg, _ = await find_last_race_box(channel)

    # Alle Bot-Bild-Posts seit dem letzten Rennkasten sammeln
    screenshots = []
    text_msgs   = []
    async for msg in channel.history(limit=200, after=last_box_msg):
        if msg.author.id != discord_client.user.id:
            continue
        has_image = any(a.content_type and a.content_type.startswith("image/")
                        for a in msg.attachments)
        if has_image:
            meta = parse_screenshot_meta_from_msg(msg)
            if meta is None:
                log.warning(f"Bot-Bild ohne Metadaten-Emojis, ueberspringe: {msg.id}")
                continue
            imgs = [a for a in msg.attachments
                    if a.content_type and a.content_type.startswith("image/")]
            screenshots.append((msg, meta, imgs[0]))
        elif not msg.embeds and msg.content:
            text_msgs.append((msg, msg.content))

    if not screenshots:
        log.info("!sort: Keine Bot-Screenshots gefunden.")
        # Textnachrichten trotzdem ans Ende
        if text_msgs:
            await _repost_texts(channel, text_msgs)
        return

    screenshots.sort(key=lambda x: screenshot_sort_key(x[1]))

    # Bilder herunterladen bevor wir loeschen
    downloaded = []
    for msg, meta, img_att in screenshots:
        img_data = requests.get(img_att.url).content
        downloaded.append((msg, meta, img_data))

    # Alle alten Bild-Posts und Textnachrichten loeschen
    for msg, _, _ in downloaded:
        try:
            await msg.delete()
        except Exception as e:
            log.warning(f"Konnte Bild-Post nicht loeschen: {e}")
        await asyncio.sleep(0.7)
    for msg, _ in text_msgs:
        try:
            await msg.delete()
        except Exception as e:
            log.warning(f"Konnte Textnachricht nicht loeschen: {e}")
        await asyncio.sleep(0.7)

    # Bilder in sortierter Reihenfolge neu posten mit Emojis
    for _, meta, img_data in downloaded:
        with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
            tmp_path = f.name
        try:
            with open(tmp_path, "wb") as f:
                f.write(img_data)
            with open(tmp_path, "rb") as f:
                img_msg = await channel.send(file=discord.File(f, filename="screenshot.png"))
            processing_ids.add(img_msg.id)
            g_emoji, p_emoji = get_marker_emojis(meta["grid"], meta["page"])
            await img_msg.add_reaction(g_emoji)
            await img_msg.add_reaction(p_emoji)
        finally:
            os.unlink(tmp_path)
        await asyncio.sleep(0.3)

    log.info(f"!sort: {len(screenshots)} Screenshots neu sortiert.")
    await update_legend(channel, downloaded)
    # Textnachrichten nach der Legende
    text_msgs.reverse()
    for _, content_txt in text_msgs:
        await channel.send(content_txt)
        await asyncio.sleep(0.3)


async def _repost_texts(channel, text_msgs):
    """Hilfsfunktion: Textnachrichten loeschen und ans Ende reposten."""
    text_msgs.reverse()
    for msg, content_txt in text_msgs:
        try:
            await msg.delete()
        except Exception:
            pass
        await channel.send(content_txt)
        await asyncio.sleep(0.3)

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

    global quota_msg  # hier deklarieren, vor allen try/except-Bloecken

    try:
        img_data = requests.get(attachment.url).content
        with open(tmp_path, "wb") as f:
            f.write(img_data)

        processing_ids.add(message.id)  # Verhindert Doppel-Scan waehrend Verarbeitung

        # Eine persistente Statusnachricht: entweder neue posten
        # oder bestehende Limit-Nachricht umschreiben
        status_msg = None
        try:
            if quota_msg:
                await quota_msg.edit(content="Screenshot wird ausgelesen...")
                status_msg = quota_msg
                quota_msg  = None
            else:
                status_msg = await channel.send("Screenshot wird ausgelesen...")
        except Exception:
            try:
                status_msg = await channel.send("Screenshot wird ausgelesen...")
            except Exception:
                pass

        try:
            data = analyse_image(tmp_path)
        except Exception:
            # status_msg wird im GeminiQuotaError-Block weiterverwendet,
            # bei anderen Fehlern loeschen
            raise  # Weiterwerfen damit except-Bloecke greifen

        sheet = get_sheet()

        # Rennnummer aus aktuellem Race-Kasten (nicht aus Screenshot)
        _, aktuelles_rennen = await find_last_race_box(channel)
        if aktuelles_rennen is None:
            aktuelles_rennen = 1
        rennen_screenshot = int(data.get("rennen", 0))
        if rennen_screenshot != aktuelles_rennen:
            log.warning(f"Rennnummer aus Screenshot ({rennen_screenshot}) "
                        f"weicht von aktuellem Rennen ({aktuelles_rennen}) ab.")

        warnings, rennen, grid_label, first_pos = write_results(
            sheet, data, rennen_override=aktuelles_rennen
        )

        # Meldung ausgeben wenn Rennnummer nicht stimmt
        if rennen_screenshot != aktuelles_rennen and rennen_screenshot != 0:
            page_tmp = 1 if (first_pos is None or first_pos == 1) else 2
            grid_str = grid_label.upper() if grid_label.isdigit() else grid_label
            await channel.send(
                f"⚠️ Screenshot Grid {grid_str} Seite {page_tmp} prüfen – "
                f"Rennnummer im Screenshot ({rennen_screenshot}) stimmt nicht "
                f"mit aktuellem Rennen ({aktuelles_rennen}) überein."
            )

        if status_msg:
            try:
                await status_msg.delete()
                status_msg = None
            except Exception:
                pass

        # Seite bestimmen: P1 = Seite 1, sonst Seite 2
        page = 1 if (first_pos is None or first_pos == 1) else 2

        for w in warnings:
            await channel.send(w)

        # Duplikat-Check: nur nach letztem Race-Kasten suchen (versiegelte Rennen nicht anfassen)
        g_emoji, p_emoji = get_marker_emojis(grid_label, page)
        last_box_for_dup, _ = await find_last_race_box(channel)
        async for old_msg in channel.history(limit=100, after=last_box_for_dup):
            old_meta = parse_screenshot_meta_from_msg(old_msg)
            if (old_meta and old_meta["grid"] == grid_label
                    and old_meta["page"] == page):
                try:
                    await old_msg.delete()
                    log.info(f"Duplikat geloescht: Grid {grid_label}, Seite {page}")
                except Exception as e:
                    log.warning(f"Konnte Duplikat nicht loeschen: {e}")
                break

        # Bild posten, dann Emojis setzen
        with open(tmp_path, "rb") as f:
            img_msg = await channel.send(file=discord.File(f, filename="screenshot.png"))
        processing_ids.add(img_msg.id)
        await img_msg.add_reaction(g_emoji)
        await img_msg.add_reaction(p_emoji)

        # Race-Kasten aktualisieren
        await update_race_box(channel, rennen)

        elapsed = asyncio.get_event_loop().time() - started
        log.info(f"Verarbeitet in {elapsed:.1f}s. {len(warnings)} Warnung(en).")
        success = True

    except GeminiQuotaError as qe:
        retry_time = berlin_time_str(gemini_blocked_until) if gemini_blocked_until else "?"
        text = f"⏳ Gemini-Limit erreicht, versuche es wieder um {retry_time} Uhr."
        # status_msg in Limit-Nachricht umwandeln statt neue zu posten
        try:
            if status_msg:
                await status_msg.edit(content=text)
                quota_msg  = status_msg
                status_msg = None
            elif quota_msg:
                await quota_msg.edit(content=text)
            else:
                quota_msg = await channel.send(text)
        except Exception:
            quota_msg = await channel.send(text)
        log.warning(f"Quota-Fehler ({qe}), Retry um {retry_time} Uhr.")
        success = None

    except Exception as e:
        log.error(f"Fehler: {e}", exc_info=True)
        await channel.send(f"Fehler: {type(e).__name__}: {str(e)[:200]}")
        success = False

    finally:
        elapsed = asyncio.get_event_loop().time() - started
        os.unlink(tmp_path)

    processing_ids.discard(message.id)
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
                await cmd_clean(channel)
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
                await cmd_clean(channel)
            embed = discord.Embed(
                description=f"**Race {rn:02d}**",
                color=0x1a1a2e
            )
            await channel.send(embed=embed)
            log.info(f"!race: Race-Kasten fuer Rennen {rn} erstellt.")
            await check_gemini_version(channel)

        elif cmd == "!check":
            await cmd_check(channel)

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
            await cmd_clean(channel)
            await channel.send("Fertig.", delete_after=10)

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
                log.info(f"Gemini gesperrt, ueberspringe Bild-Scan. Noch ca. {mins} Minuten.")
                # Befehle trotzdem verarbeiten (kein Gemini noetig)
                async for message in channel.history(limit=20):
                    if (message.content.startswith("!")
                            and message.author.id != discord_client.user.id):
                        await handle_command(message)
                # Sperre aufgehoben?
                if not gemini_is_blocked():
                    await clear_quota_msg(channel)
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
                if message.id in processing_ids:
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
                        # Kanal immer sortieren nach fertigem Post (auch Einzelpost)
                        await cmd_sort(channel)
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
    load_car_list()  # laedt auch Car_Translate
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

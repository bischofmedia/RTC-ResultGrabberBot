import os
import re
import time
import json
import asyncio
import logging
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
SPECIAL_EVENT_RAW       = os.environ.get("SPECIAL_EVENT", "")
REGISTRATION_END_TIME   = os.environ.get("REGISTRATION_END_TIME", "20:45")  # Format HH:MM
SPECIAL_EVENTS     = [s.strip().lower() for s in SPECIAL_EVENT_RAW.split(";") if s.strip()]

async def run_sync(func, *args, **kwargs):
    """Fuehrt synchrone Funktion in Thread-Pool aus um asyncio-Loop nicht zu blockieren."""
    loop = asyncio.get_event_loop()
    import functools
    return await loop.run_in_executor(None, functools.partial(func, *args, **kwargs))


POLL_INTERVAL = 15
DONE_EMOJI    = "\u2705"
ERROR_EMOJI   = "\u274c"
MANUAL_EMOJI  = "\u270d\ufe0f"  # ✍️ manuell

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
driver_map:        dict = {}
gt7_name_map:      dict = {}
discord_id_map:    dict = {}  # {discord_id: (tabellenname, team)}

class GeminiQuotaError(Exception):
    pass

# Nachrichten-IDs die gerade verarbeitet werden (verhindert Doppel-Scan)
processing_ids: set = set()

# Grid-Snapshot: {fahrername_lower: grid_label} - wird montags um REGISTRATION_END_TIME erstellt
grid_snapshot: dict = {}
grid_snapshot_rennen: int = 0  # fuer welches Rennen der Snapshot gilt
grid_snapshot_done: bool = False  # ob Snapshot diese Woche bereits erstellt wurde

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
    "penalty":    7,   # Spalte I: Penalty in Sekunden z.B. "+10"
    "totaltime":  9,   # Spalte K: TotalTime (Formelwert, Strafen einberechnet)
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
    creds_value = GOOGLE_CREDENTIALS
    if os.path.isfile(creds_value):
        with open(creds_value) as f:
            creds_dict = json.load(f)
    else:
        creds_dict = json.loads(creds_value)
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
    for versuch in range(1, 6):
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
            break
        except Exception as e:
            if "Car_Translate" in str(e) or "worksheet" in str(e).lower() or "not found" in str(e).lower():
                log.info("Car_Translate Tabellenblatt nicht vorhanden - wird ignoriert.")
                car_translate_map = {}
                break
            if versuch < 5:
                log.warning(f"Car_Translate Versuch {versuch}/5 fehlgeschlagen: {e} - warte 2s")
                import time; time.sleep(2)
            else:
                log.error(f"Car_Translate konnte nach 5 Versuchen nicht geladen werden: {e}")
                car_translate_map = {}

def load_driver_list():
    """Laedt Fahrerliste aus DB_drvr.
    Spalte C = Tabellenname, Spalte K = Team, Spalte DB = GT7-Spielname, Spalte DC = Discord-ID.
    Gibt drei Dicts zurueck:
      driver_map:     {lower_tabellenname: (tabellenname, team, discord_id_or_None)}
      gt7_name_map:   {lower_gt7name:      (tabellenname, team, discord_id_or_None)}
      discord_id_map: {discord_id:          (tabellenname, team)}
    """
    try:
        wb    = get_workbook()
        sheet = wb.worksheet("DB_drvr")

        # Spalte C+K: Tabellenname und Team
        rows_ck  = sheet.get("C5:K200")
        # Spalte DB: GT7-Spielnamen
        rows_db  = sheet.get("DB5:DB200")
        # Spalte DC (107): Discord-IDs
        rows_dc  = sheet.get("DC5:DC200")

        driver_map     = {}
        gt7_name_map   = {}
        discord_id_map = {}

        for i, row in enumerate(rows_ck):
            name = row[0].strip() if len(row) > 0 else ""
            team = row[8].strip() if len(row) > 8 else ""

            dc_row     = rows_dc[i] if i < len(rows_dc) else []
            discord_id = dc_row[0].strip() if dc_row and dc_row[0].strip() else None

            if name:
                driver_map[name.lower()] = (name, team, discord_id)
                if discord_id:
                    discord_id_map[discord_id] = (name, team)

            # GT7-Name aus Spalte DB, gleiche Zeile
            gt7_row  = rows_db[i] if i < len(rows_db) else []
            gt7_name = gt7_row[0].strip() if gt7_row else ""
            if gt7_name and name:
                gt7_name_map[gt7_name.lower()] = (name, team, discord_id)

        if not driver_map:
            log.warning("Fahrerliste ist leer! Bitte DB_drvr pruefen (Spalte C ab Zeile 5).")
        else:
            dc_count = sum(1 for v in driver_map.values() if v[2])
            log.info(f"Fahrerliste geladen: {len(driver_map)} Eintraege, "
                     f"{len(gt7_name_map)} GT7-Namen, {dc_count} Discord-IDs")
        return driver_map, gt7_name_map, discord_id_map
    except Exception as e:
        log.error(f"KRITISCH: Fahrerliste konnte nicht geladen werden: {e}")
        return {}, {}, {}

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
    """Verschiebt einen Grid-Block per Batch-Read und Batch-Write (minimal API-Calls)."""
    # Grid-Label verschieben
    sr, sc = get_grid_label_cell(rennen, src_block)
    dr, dc = get_grid_label_cell(rennen, dst_block)
    label_val = sheet.cell(sr, sc).value or ""

    # Alle Daten des src_blocks in einem Aufruf lesen
    cs = col_start(rennen)
    r_start = row_start(src_block)
    r_end   = r_start + 19
    src_range = (rowcol_to_a1(r_start, cs + REL["driver"]) + ":" +
                 rowcol_to_a1(r_end,   cs + REL["laps"]))
    src_data = sheet.get(src_range)

    # Batch-Update fuer Ziel-Block aufbauen
    dst_r_start = row_start(dst_block)
    updates = []
    # Grid-Label
    updates.append({"range": rowcol_to_a1(dr, dc), "values": [[label_val]]})
    updates.append({"range": rowcol_to_a1(sr, sc), "values": [[""]]})
    # Datenzeilen
    for i, row in enumerate(src_data):
        for j, field in enumerate(("driver", "team", "car", "racetime", "laps")):
            val = row[j] if j < len(row) else ""
            dr2, dc2 = get_cell(rennen, dst_block, i + 1, field if field != "team" else "driver")
            # team hat keinen eigenen REL-Key in get_cell, manuell:
        # Gesamte Zeile als Range
        dst_r = dst_r_start + i
        src_r = r_start + i
        n_cols = REL["laps"] - REL["driver"] + 1
        dst_range = (rowcol_to_a1(dst_r, cs + REL["driver"]) + ":" +
                     rowcol_to_a1(dst_r, cs + REL["laps"]))
        src_range_row = (rowcol_to_a1(src_r, cs + REL["driver"]) + ":" +
                         rowcol_to_a1(src_r, cs + REL["laps"]))
        row_vals = row + [""] * (n_cols - len(row)) if len(row) < n_cols else row[:n_cols]
        updates.append({"range": dst_range, "values": [row_vals]})
        updates.append({"range": src_range_row, "values": [[""]*n_cols]})

    sheet.batch_update(updates)
    log.info(f"shift_block: Block {src_block} -> {dst_block} in {len(updates)} Batch-Updates")

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
GENERATION_CONFIG = genai.GenerationConfig(temperature=0, max_output_tokens=8192)

def build_extract_prompt():
    """Erstellt den Extraktions-Prompt mit aktueller Fahrerliste."""
    # Fahrernamen aus driver_map fuer Prompt verwenden
    if driver_map:
        names = sorted(driver_map.keys())
        # Originalnamen (nicht lowercase) aus den Werten holen
        name_list = [driver_map[k][0] for k in names[:50]]  # max 50 Namen im Prompt
        names_str = ", ".join(f"'{n}'" for n in name_list)
        name_section = (
            "FAHRERNAMEN: Kopiere exakt so wie im Bild. Keine Korrekturen.\n"
            f"Bekannte Fahrer (exakt so schreiben): {names_str}\n"
            "Unbekannte Namen ebenfalls unveraendert uebernehmen.\n"
            "WICHTIG: Niemals - durch _ ersetzen oder umgekehrt.\n"
            "WICHTIG: Apostrophe immer als geraden Apostroph ' schreiben, nie als \u2019 oder `.\n\n"
        )
    else:
        name_section = (
            "FAHRERNAMEN: Kopiere exakt so wie im Bild. Keine Korrekturen.\n"
            "WICHTIG: Niemals - durch _ ersetzen oder umgekehrt.\n"
            "WICHTIG: Apostrophe immer als geraden Apostroph ' schreiben, nie als ' oder `.\n\n"
        )
    return (
        "Analysiere diesen Gran Turismo Ergebnisscreen und extrahiere die Daten als JSON.\n\n"
        "Gib NUR gueltiges JSON zurueck, kein Markdown, keine Erklaerungen.\n\n"
        + name_section +
        "FAHRZEUGNAMEN: Lies den Namen exakt so wie er im Bild steht.\n"
        "Kopiere unveraendert, inklusive Jahreszahl, Sonderzeichen und Klammern.\n"
        "WICHTIG: Apostrophe immer als geraden Apostroph ' schreiben, nie als ' oder `.\n\n"
        "Format:\n"
        "{\n"
        '  "rennen": <Zahl>,\n'
        '  "grid": "<1, 2, 2a, 2b oder 3 - oder null wenn nicht erkennbar>",\n'
        '  "kopfzeile": "<vollstaendiger Text der Kopfzeile exakt wie im Bild>",\n'
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
        "- Wenn keine Gridnummer erkennbar ist, setze grid auf null\n"
        "- kopfzeile: gesamter Titeltext der Ergebnisliste\n"
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

def repair_gemini_json(text):
    """Repariert haeufige JSON-Fehler in Gemini-Antworten."""
    # 1. Typografische Anfuehrungszeichen in Werten -> gerade
    text = text.replace("“", '"').replace("”", '"')
    text = text.replace("‘", "'").replace("’", "'")
    # 2. Fehlendes } vor , { (Gemini vergisst manchmal schliessende Klammer)
    text = re.sub(r'("|\ d)(\s*\n\s*),(\s*\{)', r'\1\2},\3', text)
    # 3. Trailing commas vor } und ]
    text = re.sub(r",\s*([}\\]])", r"\1", text)
    # 3. Einfache Anfuehrungszeichen bei Property-Namen -> doppelte
    text = re.sub(r"'([^'\n]+)'(\s*:)", r'"\1"\2', text)
    # 4. Unescapte Backslashes (ausser vor " n r t b f u)
    text = re.sub(r'\\(?!["\\/bfnrtu])', r'\\\\', text)
    # 5. Steuerzeichen in Strings entfernen (Tabs, Newlines innerhalb von Strings)
    # Ersetze echte Newlines innerhalb von JSON-String-Werten durch \n
    result = []
    in_string = False
    escape_next = False
    for ch in text:
        if escape_next:
            result.append(ch)
            escape_next = False
        elif ch == '\\':
            result.append(ch)
            escape_next = True
        elif ch == '"':
            result.append(ch)
            in_string = not in_string
        elif in_string and ch == '\n':
            result.append('\\n')
        elif in_string and ch == '\t':
            result.append('\\t')
        elif in_string and ord(ch) < 32:
            pass  # andere Steuerzeichen ignorieren
        else:
            result.append(ch)
    return "".join(result)


_gemini_rpm_strikes = 0  # Zaehlt aufeinanderfolgende RPM-Fehler fuer exponentiellen Backoff

def call_gemini(img, prompt):
    global gemini_blocked_until, _gemini_rpm_strikes
    try:
        response = gemini_model.generate_content(
            [prompt, img],
            generation_config=GENERATION_CONFIG
        )
        _gemini_rpm_strikes = 0  # Erfolg: Strikes zuruecksetzen
        text = response.text.strip()
        text = re.sub(r"^```json\s*", "", text)
        text = re.sub(r"\s*```$",     "", text)
        try:
            return json.loads(text)
        except json.JSONDecodeError as je:
            log.warning(f"JSON-Parsing fehlgeschlagen ({je})")
            log.warning(f"Rohe Gemini-Antwort: {text[:800]}")
            fixed = repair_gemini_json(text)
            try:
                return json.loads(fixed)
            except json.JSONDecodeError as je2:
                log.error(f"JSON-Reparatur fehlgeschlagen ({je2}): {fixed[:500]}")
                raise
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
            # Minutenlimit: Backoff exponentiell erhoehen (5 -> 10 -> 20 -> max 60 Min)
            _gemini_rpm_strikes += 1
            backoff = min(5 * (2 ** (_gemini_rpm_strikes - 1)), 60)
            gemini_blocked_until = datetime.now() + timedelta(minutes=backoff)
            log.warning(f"Gemini Minutenlimit erreicht (Strike {_gemini_rpm_strikes}). "
                        f"Sperre fuer {backoff} Minuten.")
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

async def download_attachment(attachment):
    """Laedt Attachment ueber den authentifizierten Discord-HTTP-Client herunter."""
    return await discord_client.http.get_from_cdn(attachment.url)

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
        import asyncio as _asyncio
        response = await _asyncio.to_thread(
            gemini_model.generate_content, prompt, generation_config=GENERATION_CONFIG
        )
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

def _analyse_image_sync(image_path):
    """Synchroner Kern der Bildanalyse - wird in Thread ausgelagert."""
    img    = Image.open(image_path)

    # Bild auf max 1600px Breite skalieren fuer kuerzere Verarbeitungszeit
    max_width = 1600
    if img.width > max_width:
        ratio = max_width / img.width
        new_h = int(img.height * ratio)
        img = img.resize((max_width, new_h), Image.LANCZOS)
        log.info(f"Bild skaliert auf {max_width}x{new_h}")

    prompt = build_extract_prompt()
    data   = call_gemini(img, prompt)
    log.info(f"Durchlauf 1: Rennen {data.get('rennen')}, Grid {data.get('grid')}, "
             f"{len(data.get('fahrer', []))} Fahrer")

    # Special Event: wenn grid null/leer und Kopfzeile enthaelt bekanntes Event -> Grid 1
    grid_val = data.get("grid")
    if not grid_val or str(grid_val).strip().lower() in ("null", "none", ""):
        kopfzeile = data.get("kopfzeile", "").lower()
        if SPECIAL_EVENTS and any(ev in kopfzeile for ev in SPECIAL_EVENTS):
            data["grid"] = "1"
            log.info(f"Special Event erkannt in Kopfzeile '{kopfzeile}' -> Grid 1")

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

    driver_map, gt7_name_map, discord_id_map = load_driver_list()

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
            name, team, _ = driver_map[name_key]
        elif name_key in gt7_name_map:
            name, team, _ = gt7_name_map[name_key]
        else:
            name = name_raw
            team = ""
            r_drv, c_drv = get_cell(rennen, block, pos, "driver")
            red_cells.append((r_drv, c_drv))
            warnings.append(
                (2, f"👤 Rennen {rennen}, Grid {grid_label}, Pos {pos}, {name_raw}: "
                f"Fahrer nicht in Fahrerliste")
            )

        racetime, laps = clean_time(zeit)

        name_log = f"{name_raw} -> {name}" if name != name_raw else name
        auto_log = f"{auto_raw} -> {auto}" if auto != auto_raw else auto
        log.info(f"  P{pos} {name_log} | {auto_log} | racetime={racetime} "
                 f"laps={laps} fl={beste_runde}")

        r_drv, c_drv = get_cell(rennen, block, pos, "driver")
        r_tm,  c_tm  = get_cell(rennen, block, pos, "team")
        r_car, c_car = get_cell(rennen, block, pos, "car")
        r_rt,  c_rt  = get_cell(rennen, block, pos, "racetime")
        r_lp,  c_lp  = get_cell(rennen, block, pos, "laps")

        batch[rowcol_to_a1(r_drv, c_drv)] = name
        batch[rowcol_to_a1(r_tm,  c_tm)]  = team
        batch[rowcol_to_a1(r_car, c_car)] = auto
        if racetime is not None:
            batch[rowcol_to_a1(r_rt, c_rt)] = racetime
        if laps is not None:
            batch[rowcol_to_a1(r_lp, c_lp)] = laps

        if auto_unbekannt:
            red_cells.append((r_car, c_car))
            warnings.append(
                (3, f"🚗 Rennen {rennen}, Grid {grid_label}, Pos {pos}, {name}: "
                f"Auto '{auto}' nicht erkannt - bitte manuell pruefen")
            )

        if pos in delta_errors:
            red_cells.append((r_rt, c_rt))
            warnings.append(
                (4, f"⏱️ Grid {grid_label}, Pos {pos}, {name}: Zeit ist zu pruefen")
            )

        if laps is not None:
            warnings.append(
                (5, f"✍️ Grid {grid_label}, Pos {pos}, {name}: Zeit muss manuell eingetragen werden.")
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

        # Sieger je Grid-Block (anhand TotalTime, Strafen beruecksichtigt)
        cs = col_start(rennen)
        winners     = []
        annotations = []  # Fussnoten fuer Abweichungen
        for block in range(4):
            gl_r, gl_c = get_grid_label_cell(rennen, block)
            gl_val     = (sheet.cell(gl_r, gl_c).value or "").strip()
            if not gl_val:
                continue

            # Alle Fahrer des Blocks lesen (max 20 Zeilen)
            r_start = row_start(block)
            block_data = sheet.get(
                rowcol_to_a1(r_start, cs + REL["driver"]) + ":" +
                rowcol_to_a1(r_start + 19, cs + REL["totaltime"])
            )

            best_time  = None
            best_name  = None
            p1_name    = None
            p1_penalty = None

            for i, row in enumerate(block_data):
                rel_drv  = 0
                rel_laps = REL["laps"]       - REL["driver"]
                rel_pen  = REL["penalty"]    - REL["driver"]
                rel_tot  = REL["totaltime"]  - REL["driver"]

                name = row[rel_drv].strip() if len(row) > rel_drv else ""
                if not name:
                    continue

                laps_val = row[rel_laps].strip() if len(row) > rel_laps else ""
                if laps_val:
                    continue  # ueberrundet - ignorieren

                tot_raw = row[rel_tot].strip() if len(row) > rel_tot else ""
                # DNF: String "DNF" oder Sheets-Zeitwert >= 8 Stunden (= 8/24 Tag)
                if not tot_raw:
                    continue
                if isinstance(tot_raw, (int, float)) and float(tot_raw) * 24 >= 8:
                    continue  # DNF-Platzhalter
                if isinstance(tot_raw, str) and ("DNF" in tot_raw.upper() or tot_raw == "8:00:00,000"):
                    continue

                # TotalTime parsen: Google Sheets liefert float (Tagesbruchteil) oder String
                try:
                    if isinstance(tot_raw, (int, float)):
                        # Sheets-Zeitwert: Bruchteil eines Tages -> Sekunden
                        t_sek = float(tot_raw) * 86400
                    else:
                        tot_clean = str(tot_raw).replace(",", ".").replace(";", ".")
                        parts = re.split(r"[:.]", tot_clean)
                        if len(parts) == 4:
                            t_sek = int(parts[0])*3600 + int(parts[1])*60 + int(parts[2]) + int(parts[3])/1000
                        elif len(parts) == 3:
                            t_sek = int(parts[0])*60 + int(parts[1]) + int(parts[2])/1000
                        else:
                            continue
                except Exception:
                    continue

                if i == 0:
                    p1_name = name
                    pen_raw = row[rel_pen] if len(row) > rel_pen else ""
                    if pen_raw not in ("", None):
                        try:
                            p1_penalty = int(float(str(pen_raw).strip()))
                        except Exception:
                            p1_penalty = None

                if best_time is None or t_sek < best_time:
                    best_time = t_sek
                    best_name = name

            if not best_name:
                continue

            # Pruefen ob P1-Fahrer != bester TotalTime-Fahrer
            if p1_name and best_name != p1_name and p1_penalty:
                winners.append(f"Grid {gl_val}: {best_name} ⚠️")
                annotations.append(
                    f"⚠️ Grid {gl_val}: {p1_name} (+{p1_penalty}s) → Sieg an {best_name}"
                )
            else:
                winners.append(f"Grid {gl_val}: {best_name}")

        if winners:
            lines.append("")
            lines.append("**Sieger der Grids 🏆**")
            lines.extend(winners)
            if annotations:
                lines.append("")
                lines.extend(annotations)

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
    embed    = await run_sync(build_race_embed, rennen)
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
        driver_map, gt7_name_map, discord_id_map = load_driver_list()

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
            await run_sync(batch_format_cells, sheet, all_grey, [])

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
            if "auto" in txt_lower and "nicht erkannt" in txt_lower:
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
        # Zitat-Posts mit Grid/Retry-Befehlen loeschen (koennen stehenbleiben)
        is_reply_cmd = (
            msg.reference is not None and
            re.match(r"(grid\s+\w+|retry)", msg.content.strip(), re.IGNORECASE)
        )
        if (not has_embed and not has_image and not is_legend_embed(msg)) or is_reply_cmd:
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


async def is_channel_sorted(channel):
    """Prueft ob Bot-Screenshots seit dem letzten Rennkasten bereits sortiert sind."""
    last_box_msg, _ = await find_last_race_box(channel)
    current_order = []
    async for msg in channel.history(limit=200, after=last_box_msg):
        if msg.author.id != discord_client.user.id:
            continue
        has_image = any(a.content_type and a.content_type.startswith("image/")
                        for a in msg.attachments)
        if has_image:
            meta = parse_screenshot_meta_from_msg(msg)
            if meta:
                current_order.append(screenshot_sort_key(meta))
    if not current_order:
        return True  # Nichts da -> nichts zu sortieren
    expected = sorted(current_order)
    return current_order == expected

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
        img_data = await download_attachment(img_att)
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

async def cmd_textsort(channel):
    """Sortiert nur Textnachrichten ans Ende (nach dem letzten Race-Kasten)."""
    last_box_msg, _ = await find_last_race_box(channel)
    text_msgs = []
    async for msg in channel.history(limit=200, after=last_box_msg):
        if msg.author.id != discord_client.user.id:
            continue
        has_image = any(a.content_type and a.content_type.startswith("image/")
                        for a in msg.attachments)
        if not has_image and not msg.embeds and msg.content:
            text_msgs.append((msg, msg.content))
    if text_msgs:
        await _repost_texts(channel, text_msgs)
        log.info(f"!textsort: {len(text_msgs)} Textnachrichten sortiert.")


async def pipeline_empty(channel):
    """Prueft ob keine unverarbeiteten User-Screenshots mehr im Channel sind."""
    last_box_msg, _ = await find_last_race_box(channel)
    async for msg in channel.history(limit=100, after=last_box_msg):
        if msg.author.id == discord_client.user.id:
            continue
        attachments = [a for a in msg.attachments
                       if a.content_type and a.content_type.startswith("image/")]
        if not attachments:
            continue
        # Pruefen ob noch unverarbeitet (kein DONE/ERROR/MANUAL Emoji vom Bot)
        has_final = False
        for reaction in msg.reactions:
            if str(reaction.emoji) in (DONE_EMOJI, ERROR_EMOJI, MANUAL_EMOJI):
                async for user in reaction.users():
                    if user.id == discord_client.user.id:
                        has_final = True
                        break
            if has_final:
                break
        if not has_final:
            return False  # Noch unverarbeitet
    return True  # Alles erledigt


# ── Reaktions-Hilfsfunktionen ─────────────────────────────────────────────────
async def already_processed(message):
    try:
        fresh = await message.channel.fetch_message(message.id)
    except Exception:
        return True
    for reaction in fresh.reactions:
        if str(reaction.emoji) in (DONE_EMOJI, ERROR_EMOJI, MANUAL_EMOJI):
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

async def remove_all_bot_reactions(message):
    """Entfernt alle Bot-Reaktionen von einer Nachricht (fuer Retry)."""
    try:
        fresh = await message.channel.fetch_message(message.id)
    except Exception:
        return
    all_emojis = (set(NUMBER_EMOJIS) | ALL_MARKER_EMOJIS |
                  {DONE_EMOJI, ERROR_EMOJI, MANUAL_EMOJI})
    for reaction in fresh.reactions:
        if str(reaction.emoji) in all_emojis:
            async for user in reaction.users():
                if user.id == discord_client.user.id:
                    try:
                        await message.remove_reaction(reaction.emoji, discord_client.user)
                    except Exception as e:
                        log.warning(f"Konnte Reaktion {reaction.emoji} nicht entfernen: {e}")

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
async def process_image(message, attachment, grid_override=None, page_override=None):
    """
    Verarbeitet ein Bild, postet es als Bot-Post und aktualisiert den Race-Kasten.
    grid_override/page_override: manuelle Vorgabe via Reply-Befehl.
    Gibt (elapsed, success) zurueck.
    """
    log.info(f"Verarbeite: {attachment.filename} von {message.author}"
             + (f" [Override: Grid {grid_override} Seite {page_override}]"
                if grid_override else ""))
    channel = message.channel
    started = asyncio.get_event_loop().time()
    success = False
    elapsed = 0

    with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
        tmp_path = f.name

    global quota_msg  # hier deklarieren, vor allen try/except-Bloecken

    try:
        img_data = await download_attachment(attachment)
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
            # Gemini-Aufruf in Thread auslagern - Event-Loop bleibt frei fuer Heartbeats
            data = await asyncio.to_thread(_analyse_image_sync, tmp_path)
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

        # Manuelle Overrides anwenden
        if grid_override is not None:
            data["grid"] = grid_override
        if page_override is not None:
            # Seite wird ueber first_pos gesteuert: Seite 1 = P1, Seite 2 = anderer erster Platz
            # Wir merken uns den Override fuer spaeter
            pass

        warnings, rennen, grid_label, first_pos = await run_sync(
            write_results, sheet, data, rennen_override=aktuelles_rennen
        )

        # Meldung ausgeben wenn Rennnummer nicht stimmt
        if rennen_screenshot != aktuelles_rennen and rennen_screenshot != 0:
            page_tmp = 1 if (first_pos is None or first_pos == 1) else 2
            grid_str = grid_label.upper() if grid_label.isdigit() else grid_label
            warnings.insert(0, (1,
                f"⚠️ Screenshot Grid {grid_str} Seite {page_tmp} prüfen – "
                f"Rennnummer im Screenshot ({rennen_screenshot}) stimmt nicht "
                f"mit aktuellem Rennen ({aktuelles_rennen}) überein."
            ))

        if status_msg:
            try:
                await status_msg.delete()
                status_msg = None
            except Exception:
                pass

        # Seite bestimmen: P1 = Seite 1, sonst Seite 2 - oder manueller Override
        if page_override is not None:
            page = page_override
        else:
            page = 1 if (first_pos is None or first_pos == 1) else 2

        # Meldungen nach Prioritaet sortieren und posten
        warnings_sorted = sorted(
            [w if isinstance(w, tuple) else (9, w) for w in warnings],
            key=lambda x: x[0]
        )
        for _, w in warnings_sorted:
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
        # Alte Quota-Nachrichten loeschen (koennen sich bei mehrfachem Limit anhaeufen)
        async for old_qmsg in channel.history(limit=50):
            if (old_qmsg.author.id == discord_client.user.id
                    and old_qmsg.content
                    and "Gemini-Limit erreicht" in old_qmsg.content
                    and old_qmsg != quota_msg):
                try:
                    await old_qmsg.delete()
                except Exception:
                    pass
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
async def cmd_boxupgrade(channel, rennen, freitext=None):
    """Editiert Race-Kasten fuer Rennen X mit aktuellen Tabellendaten."""
    log.info(f"!boxupgrade fuer Rennen {rennen} gestartet.")
    existing = await find_race_box(channel, rennen)
    embed = await run_sync(build_race_embed_upgraded, rennen, freitext)
    if existing:
        try:
            await existing.edit(embed=embed)
            log.info(f"Race-Kasten Rennen {rennen} aktualisiert.")
        except Exception as e:
            log.error(f"Konnte Race-Kasten nicht editieren: {e}")
            await channel.send(f"Fehler beim Aktualisieren von Race {rennen:02d}: {e}")
    else:
        await channel.send(embed=embed)
        log.info(f"Race-Kasten Rennen {rennen} neu erstellt (war nicht vorhanden).")


def build_race_embed_upgraded(rennen, freitext=None):
    """Wie build_race_embed, aber mit echten Grid-Siegern und Freitext-Annotation."""
    embed = build_race_embed(rennen)
    if freitext:
        # Freitext als zusaetzliche Zeile anhaengen
        desc = embed.description or ""
        desc += f"\n\n📋 {freitext}"
        embed = discord.Embed(description=desc, color=0x1a1a2e)
    return embed


# ── Grid-Snapshot und Anwesenheitspruefung ───────────────────────────────────

GRID_SNAPSHOT_COLS = {
    "1":  3,   # Spalte C
    "2":  8,   # Spalte H
    "2a": 8,   # Spalte H
    "2b": 13,  # Spalte M
    "3":  18,  # Spalte R
}
GRID_SNAPSHOT_ROWS = (6, 21)  # Zeile 6-21 (inkl.)


def make_grid_snapshot():
    """Liest Grids-Tabellenblatt aus und erstellt Snapshot {fahrername_lower: grid_label}."""
    global grid_snapshot, grid_snapshot_done
    try:
        wb    = get_workbook()
        sheet = wb.worksheet("Grids")
        snapshot = {}
        for grid_label, col in GRID_SNAPSHOT_COLS.items():
            col_letter = rowcol_to_a1(1, col)[:-1]
            vals = sheet.get(
                f"{col_letter}{GRID_SNAPSHOT_ROWS[0]}:{col_letter}{GRID_SNAPSHOT_ROWS[1]}"
            )
            for row in vals:
                name = row[0].strip() if row and row[0].strip() else ""
                if name:
                    # Discord-ID aus driver_map nachschlagen
                    entry      = driver_map.get(name.lower())
                    discord_id = entry[2] if entry else None
                    snapshot[name.lower()] = (grid_label, discord_id)
        grid_snapshot      = snapshot
        grid_snapshot_done = True
        log.info(f"Grid-Snapshot erstellt: {len(snapshot)} Fahrer")
        return True
    except Exception as e:
        log.error(f"Grid-Snapshot fehlgeschlagen: {e}")
        return False


def check_attendance(rennen):
    """
    Vergleicht Grid-Snapshot mit tatsaechlichen Ergebnissen in Blatt T.
    Abgleich primaer per Discord-ID, Fallback per Name.
    Gibt (falsche_grids, abwesend) zurueck.
    falsche_grids: [(display_name, soll_grid, ist_grid)]
    abwesend:      [display_name]
    """
    if not grid_snapshot:
        return [], []

    try:
        sheet = get_sheet()
        cs    = col_start(rennen)

        # Alle Fahrer aus Ergebnissen sammeln
        # Speichern: {name_lower: grid_label} UND {discord_id: grid_label}
        ergebnisse_name = {}
        ergebnisse_id   = {}
        for block in range(4):
            gl_r, gl_c = get_grid_label_cell(rennen, block)
            gl_val     = (sheet.cell(gl_r, gl_c).value or "").strip().lower()
            if not gl_val:
                continue
            r_start = row_start(block)
            rows = sheet.get(
                rowcol_to_a1(r_start, cs + REL["driver"]) + ":" +
                rowcol_to_a1(r_start + 19, cs + REL["laps"])
            )
            for row in rows:
                name = row[0].strip() if row and row[0].strip() else ""
                if not name:
                    continue
                ergebnisse_name[name.lower()] = gl_val
                # Discord-ID nachschlagen
                entry = driver_map.get(name.lower())
                if entry and entry[2]:
                    ergebnisse_id[entry[2]] = gl_val

        falsche_grids = []
        abwesend      = []

        for snapshot_key, (soll_grid, discord_id) in grid_snapshot.items():
            # Originalname ermitteln
            if snapshot_key in driver_map:
                display_name = driver_map[snapshot_key][0]
            elif snapshot_key in gt7_name_map:
                display_name = gt7_name_map[snapshot_key][0]
            else:
                display_name = snapshot_key

            # Abgleich: primaer per Discord-ID, Fallback per Name
            ist_grid = None
            if discord_id and discord_id in ergebnisse_id:
                ist_grid = ergebnisse_id[discord_id]
            elif snapshot_key in ergebnisse_name:
                ist_grid = ergebnisse_name[snapshot_key]

            if ist_grid is not None:
                soll_norm = soll_grid.lower().replace("a", "").replace("b", "")
                ist_norm  = ist_grid.lower().replace("a", "").replace("b", "")
                if ist_grid != soll_grid and soll_norm != ist_norm:
                    falsche_grids.append((display_name, soll_grid.upper(), ist_grid.upper()))
            else:
                abwesend.append(display_name)

        return falsche_grids, abwesend
    except Exception as e:
        log.error(f"Anwesenheitspruefung fehlgeschlagen: {e}")
        return [], []


async def post_attendance_check(channel, rennen):
    """Fuehrt Anwesenheitspruefung durch und postet Ergebnis in Channel."""
    if not grid_snapshot:
        log.info("Kein Grid-Snapshot vorhanden, ueberspringe Anwesenheitspruefung.")
        return

    falsche_grids, abwesend = await run_sync(check_attendance, rennen)

    lines = []
    for name, soll, ist in falsche_grids:
        lines.append(f"⚠️ {name}: Start in Grid {ist} statt Grid {soll}")

    if abwesend:
        if len(abwesend) == 1:
            lines.append(f"❌ Abwesend: {abwesend[0]}")
        else:
            lines.append(f"❌ Abwesend: {', '.join(abwesend[:-1])} und {abwesend[-1]}")

    if lines:
        await channel.send("\n".join(lines))
        log.info(f"Anwesenheit: {len(falsche_grids)} falsches Grid, {len(abwesend)} abwesend")
    else:
        log.info("Anwesenheitspruefung: alle Fahrer korrekt anwesend")


async def snapshot_scheduler():
    """Laeuft im Hintergrund und erstellt jeden Montag um REGISTRATION_END_TIME den Snapshot."""
    global grid_snapshot_done
    await discord_client.wait_until_ready()

    try:
        h, m = map(int, REGISTRATION_END_TIME.split(":"))
    except Exception:
        log.error(f"Ungueltige REGISTRATION_END_TIME: {REGISTRATION_END_TIME}")
        return

    log.info(f"Snapshot-Scheduler gestartet, Zielzeit: Montag {REGISTRATION_END_TIME} Uhr (Berlin)")
    last_reset_week = None

    while not discord_client.is_closed():
        try:
            try:
                from zoneinfo import ZoneInfo
                now = datetime.now(ZoneInfo("Europe/Berlin"))
            except Exception:
                now = datetime.utcnow() + timedelta(hours=2)

            current_week = now.isocalendar()[1]

            # Reset Montag um 0 Uhr: Snapshot loeschen (wird spaeter um 20:45 neu erstellt)
            if now.weekday() == 0 and now.hour == 0 and last_reset_week != current_week:
                grid_snapshot_done = False
                last_reset_week    = current_week
                log.info("Snapshot-Flag zurueckgesetzt (Montag 0 Uhr).")

            # Montag (weekday=0), Uhrzeit erreicht, noch kein Snapshot diese Woche
            time_reached = (now.hour > h) or (now.hour == h and now.minute >= m)
            if now.weekday() == 0 and time_reached and not grid_snapshot_done:
                log.info("REGISTRATION_END_TIME erreicht, erstelle Grid-Snapshot...")
                success = await run_sync(make_grid_snapshot)
                if not success:
                    log.error("Snapshot konnte nicht erstellt werden.")

        except Exception as e:
            log.error(f"Snapshot-Scheduler Fehler: {e}")

        await asyncio.sleep(60)  # jede Minute pruefen


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
            try:
                await message.delete()
            except Exception:
                pass
            if next_rn > 1:
                await cmd_clean(channel)
                if not await is_channel_sorted(channel):
                    log.info("!next: Channel unsortiert, starte !sort")
                    await cmd_sort(channel)
                else:
                    log.info("!next: Channel bereits sortiert, kein !sort noetig")
                await post_attendance_check(channel, next_rn - 1)
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
            try:
                await message.delete()
            except Exception:
                pass
            if rn > 1:
                await cmd_clean(channel)
                if not await is_channel_sorted(channel):
                    log.info("!race: Channel unsortiert, starte !sort")
                    await cmd_sort(channel)
                else:
                    log.info("!race: Channel bereits sortiert, kein !sort noetig")
                await post_attendance_check(channel, rn - 1)
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

        elif cmd == "!textsort":
            await cmd_textsort(channel)

        elif cmd == "!clean":
            await cmd_clean(channel)

        elif cmd == "!boxupgrade":
            if len(parts) < 2:
                await channel.send("Verwendung: !boxupgrade <Rennen> [Freitext]")
                return
            rn       = int(parts[1])
            freitext = " ".join(parts[2:]) if len(parts) > 2 else None
            await cmd_boxupgrade(channel, rn, freitext)

        elif cmd == "!help":
            lines = [
                "**RaceResultBot – Befehle**",
                "",
                "**!next** – Nächstes Rennen starten (Race-Kasten ++, Clean, Sort falls nötig)",
                "**!race X** – Rennen X starten (Race-Kasten auf X setzen, Clean, Sort falls nötig)",
                "**!sort** – Screenshots nach Grid/Seite sortieren",
                "**!textsort** – Nur Textnachrichten ans Ende sortieren",
                "**!clean** – Bot-Nachrichten seit letztem Race-Kasten bereinigen, aktuelles Rennen grau färben",
                "**!check** – Fahrer und Fahrzeuge validieren, Korrekturen vornehmen",
                "**!update [X]** – Fahrzeugliste neu laden; optional Race-Kasten X aktualisieren",
                "**!boxupgrade X [Freitext]** – Race-Kasten X aus Tabellendaten neu generieren (Strafen, Korrekturen)",
                "",
                "**Reply auf Screenshot mit 'Grid X Seite Y'** – Screenshot mit manuellen Werten verarbeiten",
                "**Reply auf Screenshot mit 'Grid X'** – Screenshot verarbeiten (nur wenn Gemini verfügbar)",
                "**Reply auf Screenshot mit 'Retry'** – Alle Bot-Reaktionen entfernen, Screenshot erneut auslesen",
            ]
            await channel.send("\n".join(lines))

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


async def handle_reply(message):
    """Verarbeitet Antworten auf Screenshots: 'Grid X [Seite Y]' oder 'Retry'."""
    channel = message.channel
    text    = message.content.strip()

    # Referenzierten Post laden
    try:
        ref_msg = await channel.fetch_message(message.reference.message_id)
    except Exception:
        return

    # Nur auf Posts mit Bildern reagieren
    attachments = [a for a in ref_msg.attachments
                   if a.content_type and a.content_type.startswith("image/")]
    if not attachments:
        return

    # --- Retry ---
    if text.lower() == "retry":
        await remove_all_bot_reactions(ref_msg)
        processing_ids.discard(ref_msg.id)
        log.info(f"Retry: Alle Bot-Reaktionen von {ref_msg.id} entfernt.")
        try:
            await message.delete()
        except Exception:
            pass
        return

    # --- Grid X [Seite Y] ---
    m = re.match(
        r"grid\s+(\w+)(?:\s+seite\s+(\d+))?",
        text, re.IGNORECASE
    )
    if not m:
        return

    grid_override = m.group(1).lower()  # z.B. "1", "2", "2a", "2b", "3"
    page_override = int(m.group(2)) if m.group(2) else None

    # Ohne Seite nur wenn Gemini verfuegbar
    if page_override is None and gemini_is_blocked():
        try:
            await message.delete()
        except Exception:
            pass
        await channel.send(
            f"⏳ Gemini nicht verfuegbar. Bitte 'Grid {grid_override.upper()} Seite X' "
            f"angeben damit der Screenshot manuell markiert werden kann."
        )
        return

    # Alle alten Bot-Reaktionen entfernen (Neuverarbeitung)
    await remove_all_bot_reactions(ref_msg)
    processing_ids.discard(ref_msg.id)

    if gemini_is_blocked():
        # Manuell markieren
        grid_emoji = GRID_EMOJI.get(grid_override, "❓")
        page_emoji = PAGE_EMOJI.get(page_override, "❓")
        try:
            await ref_msg.add_reaction(grid_emoji)
            await ref_msg.add_reaction(page_emoji)
            await ref_msg.add_reaction(MANUAL_EMOJI)
        except Exception as e:
            log.warning(f"Konnte Reaktionen nicht setzen: {e}")
        await channel.send(
            f"⏳ Gemini nicht verfuegbar. "
            f"Grid {grid_override.upper()} Seite {page_override} bitte manuell eintragen."
        )
        log.info(f"Manuell markiert: Grid {grid_override} Seite {page_override}")
    else:
        # Mit Override verarbeiten
        attachment = attachments[0]
        processing_ids.add(ref_msg.id)
        log.info(f"Manueller Override: Grid {grid_override} Seite {page_override}")
        _, success = await process_image(
            ref_msg, attachment,
            grid_override=grid_override,
            page_override=page_override
        )
        if success is True:
            try:
                await ref_msg.delete()
                log.info("Original-Post nach manuellem Override geloescht.")
            except Exception:
                pass
            await cmd_sort(channel)

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
                    if message.author.id == discord_client.user.id:
                        continue
                    if (message.content.startswith("!")):
                        await handle_command(message)
                    elif (message.reference and
                          re.match(r"(grid\s+\w+|retry)", message.content.strip(), re.IGNORECASE)):
                        await handle_reply(message)
                # Sperre aufgehoben?
                if not gemini_is_blocked():
                    await clear_quota_msg(channel)
                await asyncio.sleep(POLL_INTERVAL)
                continue

            async for message in channel.history(limit=50):

                # Nur Nicht-Bot-Nachrichten verarbeiten
                if message.author.id == discord_client.user.id:
                    continue

                # Befehle verarbeiten
                if message.content.startswith("!"):
                    await handle_command(message)
                    continue

                # Reply-Befehle verarbeiten (Grid X [Seite Y] oder Retry)
                if (message.reference and
                        re.match(r"(grid\s+\w+|retry)", message.content.strip(), re.IGNORECASE)):
                    await handle_reply(message)
                    continue

                # Nur fremde Posts mit Bildern auslesen
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

                attachment = attachments[next_index]
                if message.id in processing_ids:
                    continue  # Doppelcheck direkt vor dem Aufruf
                processing_ids.add(message.id)  # Vor dem Aufruf eintragen - verhindert Doppel-Scan
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
                        # textsort wenn keine weiteren Screenshots in der Pipeline
                        if await pipeline_empty(channel):
                            await cmd_textsort(channel)
                    else:
                        await message.add_reaction(NUMBER_EMOJIS[new_count - 1])
                        log.info(f"Bild {new_count}/{total} verarbeitet.")
                elif success is False:
                    await remove_number_reactions(message)
                    await message.add_reaction(ERROR_EMOJI)
                    # textsort auch bei Fehler wenn Pipeline leer
                    if await pipeline_empty(channel):
                        await cmd_textsort(channel)
                # success is None -> Quota, kein Emoji

                remaining = POLL_INTERVAL - elapsed
                if remaining > 0:
                    log.info(f"Warte {remaining:.1f}s")
                    await asyncio.sleep(remaining)
                continue  # Kein zusaetzliches Sleep am Ende

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
    global driver_map, gt7_name_map, discord_id_map
    log.info(f"Eingeloggt als {discord_client.user}")
    load_car_list()  # laedt auch Car_Translate
    driver_map, gt7_name_map, discord_id_map = load_driver_list()
    if not car_list:
        channel = discord_client.get_channel(DISCORD_CHANNEL_ID)
        if channel:
            await channel.send(
                "⚠️ Fahrzeugliste konnte nicht geladen werden (DB_Tech, Spalte R ab Zeile 8). "
                "Fahrzeugnamen werden nicht uebersetzt. Bitte !update ausfuehren nach Pruefung."
            )
    discord_client.loop.create_task(scan_channel())
    discord_client.loop.create_task(snapshot_scheduler())

async def main():
    await start_webserver()
    await discord_client.start(DISCORD_TOKEN)

if __name__ == "__main__":
    asyncio.run(main())

#!/usr/bin/env python3
"""
rtc_import_results_legacy.py
────────────────────────────
Liest Rennergebnisse aus dem Google Sheet fuer RTC-Saisons 8-11
(aelteres Sheet-Format ohne PenaltyPoints, ohne Car-Boni).

Verwendung:
  python3 rtc_import_results_legacy.py --season 11
  python3 rtc_import_results_legacy.py --season 11 --race 3
"""

import os
import re
import sys
import logging
import argparse
import urllib.request
import urllib.error
import json
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

import pymysql
from dotenv import load_dotenv
from google.oauth2 import service_account
from googleapiclient.discovery import build

# ── Konfiguration ────────────────────────────────────────────────────────────

ENV_PATH = "/etc/RTC_RaceResultBot-env"
load_dotenv(ENV_PATH)

DB_HOST         = os.getenv("DB_HOST")
BERLIN          = ZoneInfo("Europe/Berlin")
DB_USER         = os.getenv("DB_USER")
DB_PASSWORD     = os.getenv("DB_PASSWORD")
DB_NAME         = os.getenv("DB_NAME")
CREDS_PATH      = os.getenv("GOOGLE_CREDENTIALS")
DISCORD_TOKEN   = os.getenv("DISCORD_TOKEN_DATABASEBOT")
DISCORD_LOG_CH  = os.getenv("DISCORD_CHANNEL_DATABASELOG")

# Bonus-Typen (entsprechen bonus_type in bonus_points-Tabelle)
BONUS_FL      = "FL"   # Schnellste Runde
BONUS_PODIUM  = "POD"  # Podium
BONUS_SR      = "SR"   # Seltenes Fahrzeug
BONUS_FT      = "FT"   # Fahrzeugtreue

# DNF-Marker im Sheet
DNF_MARKER = "8:00:00"

# Logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler(
            os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         "rtc_import_results.log")
        ),
    ],
)
log = logging.getLogger("rtc_import")


# ── Discord-Benachrichtigung ──────────────────────────────────────────────────

def discord_notify(lines: list[str]):
    """
    Postet eine Nachricht in den Datenbank-Log-Channel via Discord REST API.
    Kein discord.py benoetigt – nur stdlib urllib.
    lines: Liste von Zeilen die zusammengefuegt werden.
    """
    if not DISCORD_TOKEN or not DISCORD_LOG_CH:
        log.warning("DISCORD_TOKEN_DATABASEBOT oder DISCORD_CHANNEL_DATABASELOG nicht gesetzt – kein Discord-Log.")
        return
    content = "\n".join(lines)
    if len(content) > 1900:
        content = content[:1900] + "\n…"
    url     = f"https://discord.com/api/v10/channels/{DISCORD_LOG_CH}/messages"
    payload = json.dumps({"content": content}).encode("utf-8")
    req     = urllib.request.Request(
        url,
        data=payload,
        headers={
            "Authorization": f"Bot {DISCORD_TOKEN}",
            "Content-Type":  "application/json",
            "User-Agent":    "RTC-ImportBot/1.0",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            if resp.status in (200, 201):
                log.info("Discord-Log gepostet.")
            else:
                log.warning(f"Discord-Log: unerwarteter Status {resp.status}")
    except urllib.error.HTTPError as e:
        log.warning(f"Discord-Log fehlgeschlagen: HTTP {e.code} – {e.read().decode()[:200]}")
    except Exception as e:
        log.warning(f"Discord-Log fehlgeschlagen: {e}")


# ── Datenbank ─────────────────────────────────────────────────────────────────

def get_db():
    return pymysql.connect(
        host=DB_HOST, user=DB_USER, password=DB_PASSWORD,
        database=DB_NAME, charset="utf8mb4",
        cursorclass=pymysql.cursors.DictCursor,
        autocommit=False,
        connect_timeout=10,
        read_timeout=30,
        write_timeout=30,
    )


# ── Google Sheets ─────────────────────────────────────────────────────────────

def get_sheets_service():
    creds = service_account.Credentials.from_service_account_file(
        CREDS_PATH,
        scopes=["https://www.googleapis.com/auth/spreadsheets.readonly"],
    )
    return build("sheets", "v4", credentials=creds, cache_discovery=False)


def fetch_sheet(service, sheet_id: str, tab: str) -> list:
    result = (
        service.spreadsheets()
        .values()
        .get(spreadsheetId=sheet_id, range=f"'{tab}'")
        .execute()
    )
    return result.get("values", [])


def list_sheet_tabs(service, sheet_id: str) -> list:
    meta = service.spreadsheets().get(spreadsheetId=sheet_id).execute()
    return [s["properties"]["title"] for s in meta["sheets"]]


def parse_info_sheet(rows: list) -> dict:
    """
    Liest den Rennkalender aus dem Info-Tabellenblatt (Legacy-Format Saisons 8-11).

    Spalten (0-basiert):
      B=1: Rennnummer (#), C=2: Datum, E=4: Track,
      F=5: Time of Day, G=6: Weather Code
      Kein Laps-Feld (wurde als Zeitrennen gespielt).

    Startzeile wird dynamisch ueber '#' in Spalte B ermittelt.
    Pausen (kein Rennnummer) werden uebersprungen.
    Time of Day: fuehrendes '(2) ' wird entfernt (GT Sport Indizierung).
    """
    # Kopfzeile suchen: Zeile mit '#' in Spalte B
    start_idx = None
    for i, row in enumerate(rows):
        val = str(row[1]).strip() if len(row) > 1 else ""
        if val == "#":
            start_idx = i + 1
            break

    if start_idx is None:
        log.warning("Info-Sheet: Kopfzeile mit '#' nicht gefunden, ueberspringe Kalender.")
        return {}

    calendar = {}
    for row in rows[start_idx:]:
        rn_raw = str(row[1]).strip() if len(row) > 1 else ""
        if not rn_raw or not rn_raw.isdigit():
            continue

        rn = int(rn_raw)

        def c(idx, default=""):
            try:
                return str(row[idx]).strip()
            except (IndexError, TypeError):
                return default

        date_raw  = c(2)
        race_date = None
        for fmt in ("%d.%m.%Y", "%Y-%m-%d"):
            try:
                race_date = datetime.strptime(date_raw, fmt).date()
                break
            except ValueError:
                pass

        # Time of Day: '(2) Sonnenuntergang/sunset' → 'Sonnenuntergang/sunset'
        time_of_day = c(5) or None
        if time_of_day and time_of_day.startswith("("):
            time_of_day = re.sub(r'^\(\d+\)\s*', '', time_of_day).strip() or None

        calendar[rn] = {
            "race_date":    race_date,
            "track_name":   c(4),
            "laps":         None,   # kein Laps-Feld in Legacy-Sheets
            "time_of_day":  time_of_day,
            "weather_code": c(6) or None,
        }

    log.info(f"Info-Sheet: {len(calendar)} Rennen im Kalender gefunden (ab Zeile {start_idx + 1}).")
    return calendar

    log.info(f"Info-Sheet: {len(calendar)} Rennen im Kalender gefunden (ab Zeile {start_idx + 1}).")
    return calendar




def cell(row: list, idx: int, default="") -> str:
    try:
        return str(row[idx]).strip()
    except IndexError:
        return default


def parse_time_to_seconds(t: str):
    """
    Konvertiert 'H:MM:SS,mmm' oder 'M:SS,mmm' in Sekunden (float).
    Gibt None zurueck bei leer, DNF oder Fehler.
    """
    if not t:
        return None
    # Komma als Dezimaltrenner -> Punkt
    t = t.replace(",", ".")
    parts = t.split(":")
    try:
        if len(parts) == 3:
            return int(parts[0]) * 3600 + int(parts[1]) * 60 + float(parts[2])
        elif len(parts) == 2:
            return int(parts[0]) * 60 + float(parts[1])
        else:
            return float(parts[0])
    except (ValueError, IndexError):
        return None


def seconds_to_timestr(sec) -> str:
    """Konvertiert Sekunden zurueck in 'H:MM:SS,mmm'."""
    if sec is None:
        return None
    h  = int(sec // 3600)
    m  = int((sec % 3600) // 60)
    s  = sec % 60
    ms = round((s - int(s)) * 1000)
    if ms == 1000:
        ms = 0
        s_int = int(s) + 1
    else:
        s_int = int(s)
    return f"{h}:{m:02d}:{s_int:02d},{ms:03d}"


def parse_penalty_seconds(s: str) -> int:
    """'+10s' oder '10s' oder '10' → 10; leer → 0."""
    if not s:
        return 0
    cleaned = s.strip().lstrip("+").rstrip("sS").strip()
    try:
        return int(cleaned)
    except ValueError:
        return 0


def parse_base_points(raw: str):
    """
    Spalte M: z.B. '¹ 59 ²'  '60 ³'  '58 ¹'  '57'

    Hochgestellte Ziffern vorne  = Schnellste-Runde-Flag (Wert egal)
    Hauptzahl in der Mitte/allein = Basispunkte
    Hochgestellte Ziffern hinten  = Podium-Bonuspunkte (der Wert)

    Rueckgabe: (base_points: int, fl_flag: int 0/1, podium_bonus: int)
    """
    if not raw:
        return 0, 0, 0

    # Superscript-Zeichen erkennen
    SUPERSCRIPT = set("¹²³⁴⁵⁶⁷⁸⁹⁰")
    SUP_TO_NUM  = str.maketrans("¹²³⁴⁵⁶⁷⁸⁹⁰", "1234567890")

    # Hat die Zeichenkette einen fuehrenden Superscript?
    has_leading_sup = bool(raw) and raw[0] in SUPERSCRIPT

    # Alle "Token-Gruppen" extrahieren: normale Ziffernfolgen vs. Superscript-Folgen
    # Wir brauchen nur die Zahlen in Reihenfolge und ob sie hochgestellt sind
    tokens = []  # Liste von (wert: int, is_superscript: bool)
    i = 0
    while i < len(raw):
        ch = raw[i]
        if ch in SUPERSCRIPT:
            j = i
            while j < len(raw) and raw[j] in SUPERSCRIPT:
                j += 1
            num_str = raw[i:j].translate(SUP_TO_NUM)
            try:
                tokens.append((int(num_str), True))
            except ValueError:
                pass
            i = j
        elif ch.isdigit():
            j = i
            while j < len(raw) and raw[j].isdigit():
                j += 1
            tokens.append((int(raw[i:j]), False))
            i = j
        else:
            i += 1

    if not tokens:
        return 0, 0, 0

    # Auswertung:
    # Moegliche Formate:
    #   [norm]                         → base=norm, fl=0, pod=0
    #   [norm, sup]                    → base=norm, fl=0, pod=sup
    #   [sup, norm]                    → fl=1, base=norm, pod=0
    #   [sup, norm, sup]               → fl=1, base=norm, pod=sup2

    normal = [(v, s) for v, s in tokens if not s]
    super_ = [(v, s) for v, s in tokens if s]

    if has_leading_sup:
        fl_flag   = 1
        base      = normal[0][0] if normal else 0
        # Podium = letzter Superscript (wenn mehr als einer vorhanden)
        trailing  = [v for v, _ in super_[1:]] if len(super_) > 1 else []
        pod_bonus = trailing[-1] if trailing else 0
    else:
        fl_flag   = 0
        base      = normal[0][0] if normal else 0
        pod_bonus = super_[-1][0] if super_ else 0

    return base, fl_flag, pod_bonus


def parse_car_bonus(raw: str):
    """'2/0' → (rare=2, loyalty=0); leer → (0,0)."""
    if not raw or "/" not in raw:
        return 0, 0
    parts = raw.split("/")
    try:
        return int(parts[0]), int(parts[1])
    except (ValueError, IndexError):
        return 0, 0


# ── DB-Lookup ─────────────────────────────────────────────────────────────────

def lookup_driver(cur, psn_name: str):
    cur.execute("SELECT driver_id FROM drivers WHERE psn_name = %s", (psn_name,))
    row = cur.fetchone()
    return row["driver_id"] if row else None


def lookup_or_create_driver(cur, psn_name: str) -> int:
    did = lookup_driver(cur, psn_name)
    if did:
        return did
    log.info(f"  Neuer Fahrer angelegt: {psn_name}")
    cur.execute(
        "INSERT INTO drivers (psn_name, is_active) VALUES (%s, 1)", (psn_name,)
    )
    return cur.lastrowid


def lookup_team(cur, name: str):
    if not name:
        return None
    cur.execute("SELECT team_id FROM teams WHERE name = %s", (name,))
    row = cur.fetchone()
    if row:
        return row["team_id"]
    # Fuzzy
    cur.execute("SELECT team_id, name FROM teams WHERE name LIKE %s LIMIT 1",
                (f"%{name}%",))
    row = cur.fetchone()
    if row:
        log.warning(f"  Team fuzzy: '{name}' → '{row['name']}'")
        return row["team_id"]
    log.warning(f"  Team nicht gefunden: '{name}'")
    return None


def lookup_vehicle(cur, name: str):
    if not name:
        return None
    cur.execute("SELECT vehicle_id FROM vehicles WHERE name = %s", (name,))
    row = cur.fetchone()
    if row:
        return row["vehicle_id"]
    # Fuzzy: erste 12 Zeichen
    cur.execute("SELECT vehicle_id, name FROM vehicles WHERE name LIKE %s LIMIT 1",
                (f"%{name[:12]}%",))
    row = cur.fetchone()
    if row:
        log.warning(f"  Fahrzeug fuzzy: '{name}' → '{row['name']}'")
        return row["vehicle_id"]
    log.warning(f"  Fahrzeug nicht gefunden: '{name}'")
    return None


def lookup_track(cur, sheet_name: str):
    """Sucht track_id anhand von tracks.sheet_name (exakt, dann getrimmt)."""
    if not sheet_name:
        return None
    cur.execute("SELECT track_id FROM tracks WHERE sheet_name = %s", (sheet_name,))
    row = cur.fetchone()
    if row:
        return row["track_id"]
    # Getrimmt versuchen (fuehrende/nachfolgende Leerzeichen im Sheet)
    cur.execute("SELECT track_id FROM tracks WHERE TRIM(sheet_name) = %s", (sheet_name.strip(),))
    row = cur.fetchone()
    if row:
        return row["track_id"]
    log.warning(f"  Strecke nicht gefunden: '{sheet_name}'")
    return None


def lookup_version_id(cur, race_date) -> int:
    """
    Ermittelt die passende version_id fuer GT7 zum Renndatum:
    Letzter GT7-Patch, dessen release_date <= race_date.
    """
    if not race_date:
        # Fallback: neueste GT7-Version
        cur.execute(
            "SELECT version_id FROM game_versions "
            "WHERE game = 'Gran Turismo 7' ORDER BY release_date DESC LIMIT 1"
        )
    else:
        cur.execute(
            "SELECT version_id FROM game_versions "
            "WHERE game = 'Gran Turismo 7' AND release_date <= %s "
            "ORDER BY release_date DESC LIMIT 1",
            (race_date,)
        )
    row = cur.fetchone()
    if row:
        return row["version_id"]
    # Absoluter Fallback: erste GT7-Version
    cur.execute(
        "SELECT version_id FROM game_versions "
        "WHERE game = 'Gran Turismo 7' ORDER BY release_date ASC LIMIT 1"
    )
    row = cur.fetchone()
    return row["version_id"] if row else 62  # 62 = GT7 1.05 Release


def lookup_or_create_race(cur, season_id: int, race_number: int, data: dict,
                          cal: dict = None):
    """
    Gibt race_id zurueck. Legt races-Eintrag an wenn nicht vorhanden.
    Bei bestehendem Eintrag: version_id wird neu berechnet und ggf. aktualisiert.
    cal: optionales Kalender-Dict aus parse_info_sheet {race_number: {...}}
    """
    cal_entry    = (cal or {}).get(race_number, {})
    track_name   = cal_entry.get("track_name") or data.get("track_name", "")
    race_date    = cal_entry.get("race_date")  or data.get("race_date")
    laps         = cal_entry.get("laps")
    time_of_day  = cal_entry.get("time_of_day")
    weather_code = cal_entry.get("weather_code")

    cur.execute(
        "SELECT race_id, version_id FROM races WHERE season_id = %s AND race_number = %s",
        (season_id, race_number),
    )
    row = cur.fetchone()

    # Korrekte version_id zum Renndatum berechnen
    correct_version_id = lookup_version_id(cur, race_date)

    if row:
        race_id            = row["race_id"]
        current_version_id = row["version_id"]
        # version_id aktualisieren wenn ein neuerer passender Patch existiert
        if correct_version_id != current_version_id:
            cur.execute(
                "UPDATE races SET version_id = %s WHERE race_id = %s",
                (correct_version_id, race_id),
            )
            log.info(
                f"  Rennen {race_number}: version_id aktualisiert "
                f"{current_version_id} → {correct_version_id}"
            )
        return race_id

    # Neu anlegen
    track_id = lookup_track(cur, track_name)
    if not track_id:
        log.error(
            f"  Rennen {race_number}: Strecke '{track_name}' nicht in DB "
            f"(sheet_name-Spalte pruefen). Rennen kann nicht angelegt werden."
        )
        return None

    cur.execute(
        """INSERT INTO races
           (season_id, track_id, version_id, race_number, race_date,
            laps, time_of_day, weather_code)
           VALUES (%s, %s, %s, %s, %s, %s, %s, %s)""",
        (season_id, track_id, correct_version_id, race_number, race_date,
         laps, time_of_day, weather_code),
    )
    race_id = cur.lastrowid
    log.info(
        f"  Rennen {race_number} neu angelegt: race_id={race_id}, "
        f"track_id={track_id}, version_id={correct_version_id}, date={race_date}, "
        f"laps={laps}, time_of_day={time_of_day}, weather={weather_code}"
    )
    return race_id


def ensure_grids(cur, race_id: int, grid_numbers: set):
    """
    Stellt sicher dass alle benoetigen Grid-Eintraege fuer race_id existieren.
    Legt fehlende Grids automatisch an.
    Grid-Labels: '1'=Grid 1, '2'=Grid 2, '3'=Grid 3
    (Splitgrids '2a'/'2b' werden nicht aus dem Sheet generiert – nur wenn explizit vorhanden)
    """
    GRID_LABELS = {
        "1": ("1", "Grid 1"),
        "2": ("2", "Grid 2"),
        "2a": ("2", "Grid 2a"),
        "2b": ("2", "Grid 2b"),
        "3": ("3", "Grid 3"),
    }
    for gn in sorted(grid_numbers):
        cur.execute(
            "SELECT grid_id FROM grids WHERE race_id = %s AND grid_number = %s",
            (race_id, gn),
        )
        if cur.fetchone():
            continue
        grid_class, grid_label = GRID_LABELS.get(gn, (gn, f"Grid {gn}"))
        cur.execute(
            "INSERT INTO grids (race_id, grid_number, grid_class, grid_label) "
            "VALUES (%s, %s, %s, %s)",
            (race_id, gn, grid_class, grid_label),
        )
        log.info(f"  Grid '{gn}' fuer race_id={race_id} angelegt.")


def lookup_grid(cur, race_id: int, grid_number: str):
    cur.execute(
        "SELECT grid_id FROM grids WHERE race_id = %s AND grid_number = %s",
        (race_id, grid_number),
    )
    row = cur.fetchone()
    return row["grid_id"] if row else None


# ── Sheet-Parsing (Legacy Format Saisons 8-11) ───────────────────────────────

def parse_race_sheet(rows: list):
    """
    Parst ein Rennen-Tabellenblatt im Legacy-Format (Saisons 8-11).

    Layout (0-basierte Zeilen-/Spaltenindizes):
      Zeile 1 (idx 1): Spalte 4 (E) = Streckenname
      Zeile 2 (idx 2): Spalte 4 (E) = Datum, Spalte 6 (G) = Schnellste Runde,
                        Spalte 8 (I) = Fahrer Schnellste Runde
      Ab Zeile 6 (idx 6): Fahrerdaten
        B=1: Pos, D=3: Driver, E=4: Team, F=5: Car,
        H=7: Grid, I=8: Strafsekunden,
        J=9: RaceTime (final, inkl. Strafabzug),
        L=11: Punkte (Basis+Boni hochgestellt)
        Kein PenaltyPoints, keine Car-Boni (SR/FT)

    Rueckgabe: dict oder None wenn leer.
    """

    def r(row_idx, col_idx, default=""):
        try:
            return str(rows[row_idx][col_idx]).strip()
        except (IndexError, TypeError):
            return default

    # Metadaten
    track_name    = r(1, 4)
    race_date_str = r(2, 4)
    fastest_lap   = r(2, 6)
    fl_driver_psn = r(2, 8)

    if not track_name and not race_date_str:
        return None

    race_date = None
    if race_date_str:
        for fmt in ("%d.%m.%Y", "%Y-%m-%d"):
            try:
                race_date = datetime.strptime(race_date_str, fmt).date()
                break
            except ValueError:
                pass
        if not race_date:
            log.warning(f"  Datum nicht parsbar: '{race_date_str}'")

    entries = []
    for row in rows[6:]:
        pos_raw = cell(row, 1)
        if not pos_raw or not pos_raw.isdigit():
            continue

        finish_pos    = int(pos_raw)
        psn_name      = cell(row, 3)
        team_name     = cell(row, 4)
        vehicle_name  = cell(row, 5)
        grid_number   = cell(row, 7)
        penalty_raw   = cell(row, 8)
        race_time_raw = cell(row, 9)   # J: RaceTime final (inkl. Strafabzug)
        points_raw    = cell(row, 11)  # L: Punkte

        if not psn_name:
            continue

        # DNF erkennen
        is_dnf = (not race_time_raw
                  or race_time_raw.startswith(DNF_MARKER)
                  or race_time_raw.upper() == "DNF")
        status = "DNF" if is_dnf else "FIN"

        # Spalte J = RaceTime MIT Strafe (finale Zeit, nach der sortiert wird)
        # race_time (ohne Strafe) = J - penalty
        race_time_sec = parse_time_to_seconds(race_time_raw) if not is_dnf else None
        penalty_sec   = parse_penalty_seconds(penalty_raw)

        if race_time_sec is not None:
            time_no_penalty = race_time_sec - penalty_sec if penalty_sec else race_time_sec
        else:
            time_no_penalty = None
        race_time_final_str = race_time_raw if not is_dnf else None

        # Punkte (keine Car-Boni in diesen Saisons)
        base_pts, fl_flag, pod_bonus = parse_base_points(points_raw)
        rare_bonus    = 0
        loyalty_bonus = 0

        try:
            pts_total = int(cell(row, 11)) if cell(row, 11).isdigit() else base_pts + pod_bonus + fl_flag
        except (ValueError, TypeError):
            pts_total = 0

        # DNF-Bonus-Fix
        if is_dnf or pts_total <= 1:
            if pts_total <= base_pts:
                fl_flag   = 0
                pod_bonus = 0

        entries.append({
            "finish_pos":        finish_pos,
            "psn_name":          psn_name,
            "team_name":         team_name,
            "vehicle_name":      vehicle_name,
            "grid_number":       grid_number,
            "penalty_sec":       penalty_sec,
            "penalty_pts":       0,
            "race_time":         seconds_to_timestr(time_no_penalty) if time_no_penalty else None,
            "race_time_final":   race_time_final_str,
            "time_no_penalty":   time_no_penalty,
            "rating":            None,
            "base_points":       base_pts,
            "fl_flag":           fl_flag,
            "podium_bonus":      pod_bonus,
            "rare_bonus":        rare_bonus,
            "loyalty_bonus":     loyalty_bonus,
            "points_total":      pts_total,
            "status":            status,
        })

    if not entries:
        return None

    # Siegerzeit ermitteln
    winner_time = None
    for e in entries:
        if e["finish_pos"] == 1 and e["time_no_penalty"] is not None:
            winner_time = e["time_no_penalty"]
            break

    # time_percent und finish_pos_grid berechnen
    from collections import defaultdict
    grid_counters = defaultdict(int)
    for entry in sorted(entries, key=lambda e: e["finish_pos"]):
        if entry["time_no_penalty"] and winner_time and winner_time > 0:
            entry["rating"] = round(entry["time_no_penalty"] / winner_time * 100, 2)
        else:
            entry["rating"] = None
        gn = entry["grid_number"]
        grid_counters[gn] += 1
        entry["finish_pos_grid"] = grid_counters[gn]

    return {
        "race_date":        race_date,
        "track_name":       track_name,
        "fastest_lap_time": fastest_lap,
        "fl_driver_psn":    fl_driver_psn,
        "fl_seconds":       parse_time_to_seconds(fastest_lap),
        "entries":          entries,
    }


# ── DB-Import ─────────────────────────────────────────────────────────────────

def import_race(cur, season_id: int, race_number: int, data: dict, cal: dict = None):
    """
    Importiert ein Rennen. Gibt dict zurueck:
      {"new": bool, "version_updated": bool, "drivers": int, "penalties": int,
       "track": str, "date": date}
    oder False bei Fehler.
    """
    # Vor lookup_or_create: Existenz und aktuelle version_id merken
    cur.execute(
        "SELECT race_id, version_id FROM races WHERE season_id = %s AND race_number = %s",
        (season_id, race_number),
    )
    existing = cur.fetchone()
    is_new_race      = existing is None
    old_version_id   = existing["version_id"] if existing else None

    race_id = lookup_or_create_race(cur, season_id, race_number, data, cal)
    if not race_id:
        return False

    # War version_id-Aenderung? Aktuelle version_id nochmal lesen
    cur.execute("SELECT version_id FROM races WHERE race_id = %s", (race_id,))
    new_version_id   = cur.fetchone()["version_id"]
    version_updated  = (not is_new_race) and (new_version_id != old_version_id)

    cal_entry    = (cal or {}).get(race_number, {})
    laps         = cal_entry.get("laps")
    time_of_day  = cal_entry.get("time_of_day")
    weather_code = cal_entry.get("weather_code")

    log.info(f"  race_id={race_id} | {len(data['entries'])} Fahrer | "
             f"Datum={data['race_date']} | Strecke={data['track_name']}")

    # Fastest-Lap-Fahrer-ID
    fl_driver_id = None
    if data["fl_driver_psn"]:
        fl_driver_id = lookup_driver(cur, data["fl_driver_psn"])
        if not fl_driver_id:
            log.warning(f"  FL-Fahrer '{data['fl_driver_psn']}' nicht in DB.")

    # races-Tabelle: alle bekannten Felder aktualisieren
    cur.execute(
        """UPDATE races SET
             race_date              = COALESCE(%s, race_date),
             fastest_lap_time       = %s,
             fastest_lap_driver_id  = %s,
             laps                   = COALESCE(%s, laps),
             time_of_day            = COALESCE(%s, time_of_day),
             weather_code           = COALESCE(%s, weather_code)
           WHERE race_id = %s""",
        (data["race_date"], data["fastest_lap_time"], fl_driver_id,
         laps, time_of_day, weather_code,
         race_id),
    )

    # Alten Stand fuer Change-Detection lesen (vor dem Loeschen)
    cur.execute(
        "SELECT driver_id, penalty_seconds, finish_pos_overall, points_total, "
        "time_percent, finish_pos_grid "
        "FROM race_results WHERE race_id = %s",
        (race_id,)
    )
    old_rows  = {r["driver_id"]: r for r in cur.fetchall()}
    old_count = len(old_rows)

    # Bestehende Ergebnisse loeschen (bonus_points zuerst wegen FK)
    cur.execute(
        "DELETE FROM bonus_points WHERE result_id IN "
        "(SELECT result_id FROM race_results WHERE race_id = %s)",
        (race_id,)
    )
    cur.execute("DELETE FROM race_results WHERE race_id = %s", (race_id,))

    # Alle benoetigten Grid-Nummern aus den Eintraegen sammeln und sicherstellen
    grid_numbers_needed = {e["grid_number"] for e in data["entries"] if e["grid_number"]}
    ensure_grids(cur, race_id, grid_numbers_needed)

    inserted          = 0
    new_penalties     = 0  # Strafen die neu sind oder sich geaendert haben
    ratings_updated   = 0  # Ratings die neu berechnet wurden oder sich geaendert haben
    grid_pos_inserted = 0  # finish_pos_grid die neu eingetragen wurden

    for entry in data["entries"]:
        psn  = entry["psn_name"]
        d_id = lookup_or_create_driver(cur, psn)
        t_id = lookup_team(cur, entry["team_name"])
        v_id = lookup_vehicle(cur, entry["vehicle_name"])
        g_id = lookup_grid(cur, race_id, entry["grid_number"])

        if not g_id:
            log.warning(
                f"  Grid '{entry['grid_number']}' fuer race_id={race_id} "
                f"nicht gefunden (Fahrer: {psn})."
            )

        bonus_total = (entry["fl_flag"] + entry["podium_bonus"]
                       + entry["rare_bonus"] + entry["loyalty_bonus"])

        if entry["rating"] is None and entry["status"] != "DNF":
            log.warning(f"  Rating nicht berechnet fuer {psn} "
                        f"(Siegerzeit nicht ermittelbar)")

        cur.execute(
            """INSERT INTO race_results
               (race_id, grid_id, driver_id, vehicle_id, team_id,
                finish_pos_overall, finish_pos_grid,
                race_time, race_time_final,
                time_percent,
                points_base, bonus_total,
                bonus_fastest_lap, bonus_podium,
                bonus_rare_vehicle, bonus_vehicle_loyalty,
                points_total, status,
                penalty_seconds, penalty_points)
               VALUES
               (%s,%s,%s,%s,%s,
                %s,%s,
                %s,%s,
                %s,
                %s,%s,
                %s,%s,
                %s,%s,
                %s,%s,
                %s,%s)""",
            (
                race_id, g_id, d_id, v_id, t_id,
                entry["finish_pos"],
                entry.get("finish_pos_grid"),
                entry["race_time"],
                entry["race_time_final"],
                entry["rating"],  # time_percent: eigene Zeit / Siegerzeit * 100
                entry["base_points"],
                bonus_total,
                1 if entry["fl_flag"] else 0,
                entry["podium_bonus"],
                entry["rare_bonus"],
                entry["loyalty_bonus"],
                entry["points_total"],
                entry["status"],
                entry["penalty_sec"],
                entry["penalty_pts"],
            ),
        )
        result_id = cur.lastrowid

        # Bonus-Eintraege
        if entry["fl_flag"]:
            cur.execute(
                "INSERT INTO bonus_points (result_id, bonus_type, points) VALUES (%s,%s,%s)",
                (result_id, BONUS_FL, 1),
            )
        if entry["podium_bonus"]:
            cur.execute(
                "INSERT INTO bonus_points (result_id, bonus_type, points) VALUES (%s,%s,%s)",
                (result_id, BONUS_PODIUM, entry["podium_bonus"]),
            )
        if entry["rare_bonus"]:
            cur.execute(
                "INSERT INTO bonus_points (result_id, bonus_type, points) VALUES (%s,%s,%s)",
                (result_id, BONUS_SR, entry["rare_bonus"]),
            )
        if entry["loyalty_bonus"]:
            cur.execute(
                "INSERT INTO bonus_points (result_id, bonus_type, points) VALUES (%s,%s,%s)",
                (result_id, BONUS_FT, entry["loyalty_bonus"]),
            )

        # Change-Detection: Strafe neu oder geaendert?
        pen = entry["penalty_sec"] or 0
        if pen > 0:
            old_pen = (old_rows.get(d_id) or {}).get("penalty_seconds") or 0
            if old_pen != pen:
                new_penalties += 1

        # Change-Detection: time_percent neu oder geaendert?
        old = old_rows.get(d_id) or {}
        new_rating = entry["rating"]
        old_rating = old.get("time_percent")
        if new_rating is not None and (old_rating is None or
                abs(float(old_rating) - float(new_rating)) > 0.01):
            ratings_updated += 1

        # Change-Detection: finish_pos_grid neu eingetragen?
        new_gpg = entry.get("finish_pos_grid")
        old_gpg = old.get("finish_pos_grid")
        if new_gpg is not None and old_gpg is None:
            grid_pos_inserted += 1

        inserted += 1

    # Echte Aenderung: neue Fahrer, Strafen, Rating, GridPos, oder Spielversion
    something_changed = (
        is_new_race
        or version_updated
        or new_penalties > 0
        or ratings_updated > 0
        or grid_pos_inserted > 0
        or inserted != old_count
    )

    log.info(f"  ✓ {inserted} Fahrer eingetragen."
             + (" (keine Aenderung)" if not something_changed else ""))
    return {
        "new":              is_new_race,
        "version_updated":  version_updated,
        "changed":          something_changed,
        "drivers":          inserted,
        "penalties":        new_penalties,
        "ratings_updated":  ratings_updated,
        "grid_pos_inserted": grid_pos_inserted,
        "track":            data["track_name"],
        "date":             data["race_date"],
    }


def _post_discord_summary(season_name: str, changes: list, errors: int):
    """
    Baut die Discord-Nachricht aus den Import-Ergebnissen und postet sie.
    changes: Liste von (race_number, result_dict)
    """
    lines = [f"🗄️ **DB-Update {season_name}**"]

    for rn, r in changes:
        track    = r.get("track", "?")
        date     = r.get("date")
        date_str = date.strftime("%d.%m.%Y") if date else ""

        if r.get("new"):
            lines.append(
                f"  ✅ Rennen {rn} erfasst – {track}"
                + (f" ({date_str})" if date_str else "")
                + f", {r['drivers']} Fahrer"
            )
        else:
            parts = []
            if r.get("penalties"):
                n = r["penalties"]
                parts.append(f"{n} Strafe{'n' if n != 1 else ''} aktualisiert")
            if r.get("ratings_updated"):
                n = r["ratings_updated"]
                parts.append(f"{n} Rating{'s' if n != 1 else ''} aktualisiert")
            if r.get("grid_pos_inserted"):
                n = r["grid_pos_inserted"]
                parts.append(f"{n} Gridposition{'en' if n != 1 else ''} eingetragen")
            if r.get("version_updated"):
                parts.append("Spielversion aktualisiert")
            if not parts:
                parts.append("Ergebnisse aktualisiert")
            lines.append(f"  🔄 Rennen {rn} – {', '.join(parts)}")

    if errors:
        lines.append(f"  ⚠️ {errors} Fehler – Details im Log prüfen.")

    discord_notify(lines)


# ── Hauptprogramm ─────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="RTC Sheet → DB Import")
    parser.add_argument("--season", type=int, default=None,
                        help="Season-ID (Standard: aktive Saison)")
    parser.add_argument("--race", type=int, default=None,
                        help="Nur dieses Rennen importieren (1-16)")
    args = parser.parse_args()

    db  = get_db()
    cur = db.cursor()

    try:
        # Saison ermitteln
        if args.season:
            cur.execute(
                "SELECT season_id, name, sheet_id FROM seasons WHERE season_id = %s",
                (args.season,)
            )
        else:
            cur.execute(
                "SELECT season_id, name, sheet_id FROM seasons WHERE is_active = 1 LIMIT 1"
            )

        season = cur.fetchone()
        if not season:
            log.error("Keine passende Saison gefunden.")
            sys.exit(1)

        season_id = season["season_id"]
        sheet_id  = season["sheet_id"]

        # Sicherungssperre: nur Saisons 8-11 sind im Legacy-Format
        if season_id < 8 or season_id > 11:
            log.error(
                f"Saison {season_id} ({season['name']}) wird von diesem Script nicht "
                f"unterstuetzt. Legacy-Format gilt nur fuer season_id 8-11."
            )
            sys.exit(1)

        if not sheet_id:
            log.error(f"Keine sheet_id in seasons fuer Saison {season_id} hinterlegt!")
            sys.exit(1)

        log.info(f"Saison: {season['name']} (ID={season_id}) | Sheet={sheet_id}")

        svc = get_sheets_service()

        # Info-Tab-Name ermitteln: Saison 8 hat abweichenden Tab-Namen
        INFO_TAB_NAMES = ["Info", "RTC_S2_2022"]
        all_tabs = list_sheet_tabs(svc, sheet_id)
        info_tab = next((t for t in INFO_TAB_NAMES if t in all_tabs), None)

        # Info-Sheet laden (Rennkalender)
        cal = {}
        if info_tab:
            try:
                info_rows = fetch_sheet(svc, sheet_id, info_tab)
                cal = parse_info_sheet(info_rows)
            except Exception as e:
                log.warning(f"Info-Sheet '{info_tab}' konnte nicht geladen werden: {e} – fahre ohne Kalender fort.")
        else:
            log.warning(f"Kein Info-Tab gefunden (gesucht: {INFO_TAB_NAMES}) – fahre ohne Kalender fort.")

        # Datum-Fenster-Check entfaellt fuer Legacy-Saisons (werden nur manuell importiert)

        # Verfuegbare numerische Tabs ermitteln (dedupliziert)
        tabs = list_sheet_tabs(svc, sheet_id)
        log.info(f"Alle Sheet-Tabs: {tabs}")
        seen = set()
        race_tabs = []
        for t in tabs:
            if t.strip().isdigit() and t.strip() not in seen:
                seen.add(t.strip())
                race_tabs.append(t.strip())
        race_tabs.sort(key=lambda x: int(x))

        if args.race:
            if str(args.race) not in race_tabs:
                log.error(f"Tab '{args.race}' nicht im Sheet gefunden (verfuegbar: {race_tabs}).")
                sys.exit(1)
            race_tabs = [str(args.race)]

        log.info(f"Zu importierende Tabs: {race_tabs}")

        imported  = 0
        skipped   = 0
        errors    = 0
        changes   = []   # Sammlung fuer Discord-Log

        for tab in race_tabs:
            race_number = int(tab)
            log.info(f"── Tab '{tab}' (Rennen {race_number}) ──────────────")

            rows = fetch_sheet(svc, sheet_id, tab)
            data = parse_race_sheet(rows)

            if not data:
                log.info(f"  Leer oder kein Ergebnis – uebersprungen.")
                skipped += 1
                continue

            result = import_race(cur, season_id, race_number, data, cal)
            if result is False:
                errors += 1
            else:
                imported += 1
                if result.get("changed"):
                    changes.append((race_number, result))

        db.commit()
        log.info(
            f"✓ Import abgeschlossen: {imported} importiert, "
            f"{skipped} uebersprungen, {errors} Fehler."
        )

        # Discord-Log nur wenn etwas passiert ist
        if changes:
            _post_discord_summary(season["name"], changes, errors)
        elif errors:
            discord_notify([f"⚠️ **DB-Import {season['name']}** – {errors} Fehler aufgetreten, nichts importiert."])

        if errors:
            sys.exit(1)

    except KeyboardInterrupt:
        db.rollback()
        log.info("Abgebrochen.")
        sys.exit(0)
    except Exception as e:
        db.rollback()
        log.exception(f"Kritischer Fehler: {e}")
        sys.exit(1)
    finally:
        cur.close()
        db.close()


if __name__ == "__main__":
    main()

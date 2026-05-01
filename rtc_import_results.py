#!/usr/bin/env python3
"""
rtc_import_results.py
─────────────────────
Liest Rennergebnisse aus dem Google Sheet einer RTC-Saison
und schreibt sie in die MariaDB (upsert: loeschen + neu eintragen).

Verwendung:
  python3 rtc_import_results.py               # aktive Saison, alle Rennen
  python3 rtc_import_results.py --season 12   # bestimmte Saison, alle Rennen
  python3 rtc_import_results.py --race 3      # aktive Saison, nur Rennen 3
  python3 rtc_import_results.py --season 12 --race 3

Cron (4 Uhr Berlin = 2 Uhr UTC, laeuft dienstags nach dem Rennen):
  0 2 * * 2 /usr/bin/python3 /home/ubuntu/RTC_RaceResultBot/rtc_import_results.py
"""

import os
import re
import sys
import logging
import argparse
from datetime import datetime

import pymysql
from dotenv import load_dotenv
from google.oauth2 import service_account
from googleapiclient.discovery import build

# ── Konfiguration ────────────────────────────────────────────────────────────

ENV_PATH = "/etc/RTC_RaceResultBot-env"
load_dotenv(ENV_PATH)

DB_HOST     = os.getenv("DB_HOST")
DB_USER     = os.getenv("DB_USER")
DB_PASSWORD = os.getenv("DB_PASSWORD")
DB_NAME     = os.getenv("DB_NAME")
CREDS_PATH  = os.getenv("GOOGLE_CREDENTIALS")

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


# ── Datenbank ─────────────────────────────────────────────────────────────────

def get_db():
    return pymysql.connect(
        host=DB_HOST, user=DB_USER, password=DB_PASSWORD,
        database=DB_NAME, charset="utf8mb4",
        cursorclass=pymysql.cursors.DictCursor,
        autocommit=False,
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


# ── Hilfsfunktionen ───────────────────────────────────────────────────────────

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


def lookup_or_create_race(cur, season_id: int, race_number: int, data: dict):
    """
    Gibt race_id zurueck. Legt races-Eintrag an wenn nicht vorhanden.
    Benoetigt track_name und race_date aus data.
    """
    cur.execute(
        "SELECT race_id FROM races WHERE season_id = %s AND race_number = %s",
        (season_id, race_number),
    )
    row = cur.fetchone()
    if row:
        return row["race_id"]

    # Neu anlegen
    track_id   = lookup_track(cur, data["track_name"])
    version_id = lookup_version_id(cur, data["race_date"])

    if not track_id:
        log.error(
            f"  Rennen {race_number}: Strecke '{data['track_name']}' nicht in DB "
            f"(sheet_name-Spalte pruefen). Rennen kann nicht angelegt werden."
        )
        return None

    cur.execute(
        """INSERT INTO races
           (season_id, track_id, version_id, race_number, race_date)
           VALUES (%s, %s, %s, %s, %s)""",
        (season_id, track_id, version_id, race_number, data["race_date"]),
    )
    race_id = cur.lastrowid
    log.info(
        f"  Rennen {race_number} neu angelegt: race_id={race_id}, "
        f"track_id={track_id}, version_id={version_id}, date={data['race_date']}"
    )
    return race_id


def lookup_grid(cur, race_id: int, grid_number: str):
    cur.execute(
        "SELECT grid_id FROM grids WHERE race_id = %s AND grid_number = %s",
        (race_id, grid_number),
    )
    row = cur.fetchone()
    return row["grid_id"] if row else None


# ── Sheet-Parsing ─────────────────────────────────────────────────────────────

def parse_race_sheet(rows: list):
    """
    Parst ein Rennen-Tabellenblatt.

    Layout (0-basierte Zeilen-/Spaltenindizes):
      Zeile 1 (idx 1): Spalte 3 (D) = Streckenname (merged E2:K2, Index 3 in 0-Basis)
      Zeile 2 (idx 2): Spalte 4 (E) = Datum, Spalte 6 (G) = Schnellste Runde,
                        Spalte 8 (I) = Fahrer Schnellste Runde
      Ab Zeile 6 (idx 6): Fahrerdaten
        Spalte 1 = Pos, 3 = Driver, 4 = Team, 5 = Car, 6 = Livery,
        7 = Grid, 8 = Penalty, 9 = PenaltyPoints, 10 = RaceTime (final),
        12 = Punkte (Basis+Boni hochgestellt), 13 = Car-Bonus, 14 = Gesamt

    Rueckgabe: dict oder None wenn leer.
    """

    def r(row_idx, col_idx, default=""):
        try:
            return str(rows[row_idx][col_idx]).strip()
        except (IndexError, TypeError):
            return default

    # Metadaten
    track_name    = r(1, 3)   # Spalte D in Zeile 2
    race_date_str = r(2, 4)   # Spalte E in Zeile 3
    fastest_lap   = r(2, 6)   # Spalte G in Zeile 3
    fl_driver_psn = r(2, 8)   # Spalte I in Zeile 3

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

    fl_seconds = parse_time_to_seconds(fastest_lap)

    entries = []
    for row in rows[6:]:  # ab Zeile 7 (Index 6)
        pos_raw = cell(row, 1)
        if not pos_raw or not pos_raw.isdigit():
            continue

        finish_pos   = int(pos_raw)
        psn_name     = cell(row, 3)
        team_name    = cell(row, 4)
        vehicle_name = cell(row, 5)
        livery_code  = cell(row, 6)
        grid_number  = cell(row, 7)
        penalty_raw  = cell(row, 8)
        penalty_pts  = cell(row, 9)
        race_time_raw = cell(row, 10)
        points_raw   = cell(row, 12)
        car_bonus_raw = cell(row, 13)
        points_total = cell(row, 14)

        if not psn_name:
            continue

        # DNF erkennen
        is_dnf = (not race_time_raw
                  or race_time_raw.startswith(DNF_MARKER)
                  or race_time_raw.upper() == "DNF")
        status = "DNF" if is_dnf else "FIN"

        # Zeiten
        race_time_sec = parse_time_to_seconds(race_time_raw) if not is_dnf else None
        penalty_sec   = parse_penalty_seconds(penalty_raw)

        # Zeit ohne Strafe (fuer Rating-Berechnung)
        if race_time_sec is not None:
            time_no_penalty = race_time_sec - penalty_sec if penalty_sec else race_time_sec
        else:
            time_no_penalty = None

        # Rating = RaceTime_ohne_Strafe / Schnellste_Runde
        rating = None
        if time_no_penalty and fl_seconds and fl_seconds > 0:
            rating = round(time_no_penalty / fl_seconds, 4)

        # Punkte
        base_pts, fl_flag, pod_bonus = parse_base_points(points_raw)
        rare_bonus, loyalty_bonus    = parse_car_bonus(car_bonus_raw)

        try:
            pts_total = int(points_total)
        except (ValueError, TypeError):
            pts_total = 0

        try:
            pen_pts = int(penalty_pts)
        except (ValueError, TypeError):
            pen_pts = 0

        entries.append({
            "finish_pos":        finish_pos,
            "psn_name":          psn_name,
            "team_name":         team_name,
            "vehicle_name":      vehicle_name,
            "livery_code":       livery_code or None,
            "grid_number":       grid_number,
            "penalty_sec":       penalty_sec,
            "penalty_pts":       pen_pts,
            # race_time = Zeit ohne Strafe (Roh-Rennzeit)
            "race_time":         seconds_to_timestr(time_no_penalty) if time_no_penalty else None,
            # race_time_final = Zeit mit Strafe (wie im Sheet in Spalte K)
            "race_time_final":   race_time_raw if not is_dnf else None,
            "rating":            rating,
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

    return {
        "race_date":        race_date,
        "track_name":       track_name,
        "fastest_lap_time": fastest_lap,
        "fl_driver_psn":    fl_driver_psn,
        "fl_seconds":       fl_seconds,
        "entries":          entries,
    }


# ── DB-Import ─────────────────────────────────────────────────────────────────

def import_race(cur, season_id: int, race_number: int, data: dict):
    race_id = lookup_or_create_race(cur, season_id, race_number, data)
    if not race_id:
        return False

    log.info(f"  race_id={race_id} | {len(data['entries'])} Fahrer | "
             f"Datum={data['race_date']} | Strecke={data['track_name']}")

    # Fastest-Lap-Fahrer-ID
    fl_driver_id = None
    if data["fl_driver_psn"]:
        fl_driver_id = lookup_driver(cur, data["fl_driver_psn"])
        if not fl_driver_id:
            log.warning(f"  FL-Fahrer '{data['fl_driver_psn']}' nicht in DB.")

    # races-Tabelle: Datum und Schnellste-Runde aktualisieren
    cur.execute(
        """UPDATE races SET
             race_date              = COALESCE(%s, race_date),
             fastest_lap_time       = %s,
             fastest_lap_driver_id  = %s
           WHERE race_id = %s""",
        (data["race_date"], data["fastest_lap_time"], fl_driver_id, race_id),
    )

    # Bestehende Ergebnisse loeschen (bonus_points zuerst wegen FK)
    cur.execute(
        "DELETE FROM bonus_points WHERE result_id IN "
        "(SELECT result_id FROM race_results WHERE race_id = %s)",
        (race_id,)
    )
    cur.execute("DELETE FROM race_results WHERE race_id = %s", (race_id,))

    inserted = 0
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

        cur.execute(
            """INSERT INTO race_results
               (race_id, grid_id, driver_id, vehicle_id, team_id,
                finish_pos_overall,
                race_time, race_time_final,
                rating_at_race,
                points_base, bonus_total,
                bonus_fastest_lap, bonus_podium,
                bonus_rare_vehicle, bonus_vehicle_loyalty,
                points_total, status,
                penalty_seconds, penalty_points,
                livery_code)
               VALUES
               (%s,%s,%s,%s,%s,
                %s,
                %s,%s,
                %s,
                %s,%s,
                %s,%s,
                %s,%s,
                %s,%s,
                %s,%s,
                %s)""",
            (
                race_id, g_id, d_id, v_id, t_id,
                entry["finish_pos"],
                entry["race_time"],
                entry["race_time_final"],
                entry["rating"],
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
                entry["livery_code"],
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
        inserted += 1

    log.info(f"  ✓ {inserted} Fahrer eingetragen.")
    return True


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

        if not sheet_id:
            log.error(f"Keine sheet_id in seasons fuer Saison {season_id} hinterlegt!")
            sys.exit(1)

        log.info(f"Saison: {season['name']} (ID={season_id}) | Sheet={sheet_id}")

        svc = get_sheets_service()

        # Verfuegbare numerische Tabs ermitteln
        tabs = list_sheet_tabs(svc, sheet_id)
        race_tabs = sorted([t for t in tabs if t.isdigit()], key=lambda x: int(x))

        if args.race:
            if str(args.race) not in race_tabs:
                log.error(f"Tab '{args.race}' nicht im Sheet gefunden (verfuegbar: {race_tabs}).")
                sys.exit(1)
            race_tabs = [str(args.race)]

        log.info(f"Zu importierende Tabs: {race_tabs}")

        imported = 0
        skipped  = 0
        errors   = 0

        for tab in race_tabs:
            race_number = int(tab)
            log.info(f"── Tab '{tab}' (Rennen {race_number}) ──────────────")

            rows = fetch_sheet(svc, sheet_id, tab)
            data = parse_race_sheet(rows)

            if not data:
                log.info(f"  Leer oder kein Ergebnis – uebersprungen.")
                skipped += 1
                continue

            ok = import_race(cur, season_id, race_number, data)
            if ok:
                imported += 1
            else:
                errors += 1

        db.commit()
        log.info(
            f"✓ Import abgeschlossen: {imported} importiert, "
            f"{skipped} uebersprungen, {errors} Fehler."
        )
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

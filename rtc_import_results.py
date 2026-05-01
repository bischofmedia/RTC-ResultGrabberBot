#!/usr/bin/env python3
"""
rtc_import_results.py
─────────────────────
Liest Rennergebnisse aus dem Google Sheet einer RTC-Saison
und schreibt sie in die MariaDB (upsert).

Verwendung:
  python3 rtc_import_results.py               # aktive Saison
  python3 rtc_import_results.py --season 12   # bestimmte Saison
  python3 rtc_import_results.py --race 3      # nur Rennen 3 (aktive Saison)
  python3 rtc_import_results.py --season 12 --race 3

Automatischer Start:
  Cron: 0 2 * * 2 /usr/bin/python3 /home/ubuntu/RTC_RaceResultBot/rtc_import_results.py
  (02:00 UTC = 03:00/04:00 Berliner Zeit je nach Sommerzeit)
  Trigger aus RaceResultBot: subprocess.run(['python3', SCRIPT_PATH])
"""

import os
import re
import sys
import json
import logging
import argparse
import subprocess
from datetime import datetime, date
from zoneinfo import ZoneInfo

import pymysql
from google.oauth2 import service_account
from googleapiclient.discovery import build
from dotenv import load_dotenv

# ── Konfiguration ────────────────────────────────────────────────────────────

ENV_PATH = "/etc/RTC_RaceResultBot-env"
load_dotenv(ENV_PATH)

DB_HOST     = os.getenv("DB_HOST")
DB_USER     = os.getenv("DB_USER")
DB_PASSWORD = os.getenv("DB_PASSWORD")
DB_NAME     = os.getenv("DB_NAME")
CREDS_PATH  = os.getenv("GOOGLE_CREDENTIALS")

BERLIN = ZoneInfo("Europe/Berlin")

# Logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("/home/ubuntu/RTC_RaceResultBot/rtc_import_results.log"),
    ],
)
log = logging.getLogger("rtc_import")

# DNF-Marker im Sheet
DNF_TIME = "8:00:00,000"

# Bonus-Typen
BONUS_FASTEST_LAP    = "FL"   # schnellste Runde
BONUS_PODIUM         = "POD"  # Podium
BONUS_RARE_VEHICLE   = "SR"   # seltenes Fahrzeug
BONUS_VEHICLE_LOYALTY = "FT"  # Fahrzeugtreue


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


def fetch_sheet(service, sheet_id: str, tab: str) -> list[list]:
    """Gibt alle Zellen des Tabellenblatts zurück (als 2D-Liste)."""
    result = (
        service.spreadsheets()
        .values()
        .get(spreadsheetId=sheet_id, range=f"'{tab}'")
        .execute()
    )
    return result.get("values", [])


def list_sheet_tabs(service, sheet_id: str) -> list[str]:
    meta = service.spreadsheets().get(spreadsheetId=sheet_id).execute()
    return [s["properties"]["title"] for s in meta["sheets"]]


# ── Hilfsfunktionen ───────────────────────────────────────────────────────────

def cell(row: list, idx: int, default="") -> str:
    """Gibt Zellinhalt zurück, stripped; leer wenn nicht vorhanden."""
    try:
        return str(row[idx]).strip()
    except IndexError:
        return default


def parse_time_to_seconds(t: str) -> float | None:
    """
    Konvertiert Zeitstring  H:MM:SS,mmm  oder  M:SS,mmm  in Sekunden.
    Gibt None zurück wenn DNF oder leer.
    """
    if not t or t == DNF_TIME:
        return None
    t = t.replace(",", ".")
    parts = t.split(":")
    try:
        if len(parts) == 3:
            h, m, s = parts
            return int(h) * 3600 + int(m) * 60 + float(s)
        elif len(parts) == 2:
            m, s = parts
            return int(m) * 60 + float(s)
        else:
            return float(parts[0])
    except ValueError:
        return None


def parse_penalty_seconds(s: str) -> int:
    """'+10s' oder '10s' oder '10' → 10; leer → 0."""
    if not s:
        return 0
    s = s.strip().lstrip("+").rstrip("s").strip()
    try:
        return int(s)
    except ValueError:
        return 0


def parse_base_points(raw: str) -> tuple[int, int, int]:
    """
    Spalte M: z.B.  '¹ 59 ²'  '60 ³'  '58 ¹'  '57'
    Superscript vorne = Schnellste-Runde-Bonus-Indikator (Wert egal, nur Flag)
    Zahl in der Mitte = Basispunkte
    Superscript hinten = Podium-Bonuspunkte (der Wert selbst)

    Gibt zurück: (base_points, fl_flag 0/1, podium_bonus_points)
    """
    # Superscript-Zeichen → normale Ziffern
    sup_map = str.maketrans("¹²³⁴⁵⁶⁷⁸⁹⁰", "1234567890 ")
    cleaned = raw.translate(sup_map).strip()

    # Teile aufsplitten: optional führende Zahl, Basispunkte, optional hintere Zahl
    # Format kann sein: "1 59 2"  "60 3"  "58 1"  "57"
    tokens = cleaned.split()
    tokens = [t for t in tokens if t.isdigit()]

    if not tokens:
        return 0, 0, 0

    # Wenn genau ein Token → nur Basispunkte, kein Bonus
    if len(tokens) == 1:
        return int(tokens[0]), 0, 0

    # Originaler Raw-String prüfen: führt er mit Superscript-Zeichen?
    has_leading_sup = raw[0] in "¹²³⁴⁵⁶⁷⁸⁹"

    if has_leading_sup and len(tokens) >= 2:
        # erstes Token = FL-Bonus-Indikator (ignorieren als Zahl, nur Flag setzen)
        # letztes Token = Podium-Bonus, Token davor = Basispunkte
        if len(tokens) == 2:
            base = int(tokens[1])
            podium = 0
            fl_flag = 1
        else:  # 3 tokens
            base = int(tokens[1])
            podium = int(tokens[2])
            fl_flag = 1
    else:
        # kein führender Superscript
        base = int(tokens[0])
        podium = int(tokens[1]) if len(tokens) > 1 else 0
        fl_flag = 0

    return base, fl_flag, podium


def parse_car_bonus(raw: str) -> tuple[int, int]:
    """
    Spalte N: '2/0' → (rare_vehicle=2, vehicle_loyalty=0)
    """
    if not raw or "/" not in raw:
        return 0, 0
    parts = raw.split("/")
    try:
        return int(parts[0]), int(parts[1])
    except (ValueError, IndexError):
        return 0, 0


# ── DB-Lookup-Funktionen ──────────────────────────────────────────────────────

def lookup_driver(cur, psn_name: str) -> int | None:
    cur.execute("SELECT driver_id FROM drivers WHERE psn_name = %s", (psn_name,))
    row = cur.fetchone()
    return row["driver_id"] if row else None


def lookup_or_create_driver(cur, psn_name: str) -> int:
    driver_id = lookup_driver(cur, psn_name)
    if driver_id:
        return driver_id
    log.info(f"  Neuer Fahrer angelegt: {psn_name}")
    cur.execute(
        "INSERT INTO drivers (psn_name, is_active) VALUES (%s, 1)", (psn_name,)
    )
    return cur.lastrowid


def lookup_team(cur, team_name: str) -> int | None:
    if not team_name:
        return None
    cur.execute("SELECT team_id FROM teams WHERE name = %s", (team_name,))
    row = cur.fetchone()
    if row:
        return row["team_id"]
    # Fuzzy: LIKE
    cur.execute("SELECT team_id, name FROM teams WHERE name LIKE %s", (f"%{team_name}%",))
    row = cur.fetchone()
    if row:
        log.warning(f"  Team fuzzy-match: '{team_name}' → '{row['name']}'")
        return row["team_id"]
    log.warning(f"  Team nicht gefunden: '{team_name}'")
    return None


def lookup_vehicle(cur, vehicle_name: str) -> int | None:
    if not vehicle_name:
        return None
    cur.execute("SELECT vehicle_id FROM vehicles WHERE name = %s", (vehicle_name,))
    row = cur.fetchone()
    if row:
        return row["vehicle_id"]
    # Fuzzy
    cur.execute(
        "SELECT vehicle_id, name FROM vehicles WHERE name LIKE %s LIMIT 1",
        (f"%{vehicle_name[:10]}%",),
    )
    row = cur.fetchone()
    if row:
        log.warning(f"  Fahrzeug fuzzy-match: '{vehicle_name}' → '{row['name']}'")
        return row["vehicle_id"]
    log.warning(f"  Fahrzeug nicht gefunden: '{vehicle_name}'")
    return None


def lookup_race(cur, season_id: int, race_number: int) -> int | None:
    cur.execute(
        "SELECT race_id FROM races WHERE season_id = %s AND race_number = %s",
        (season_id, race_number),
    )
    row = cur.fetchone()
    return row["race_id"] if row else None


def lookup_grid(cur, race_id: int, grid_number: str) -> int | None:
    cur.execute(
        "SELECT grid_id FROM grids WHERE race_id = %s AND grid_number = %s",
        (race_id, grid_number),
    )
    row = cur.fetchone()
    return row["grid_id"] if row else None


# ── Sheet-Parsing ─────────────────────────────────────────────────────────────

def parse_race_sheet(rows: list[list]) -> dict | None:
    """
    Liest ein Renn-Tabellenblatt und gibt ein Dict zurück:
    {
      'race_date': date,
      'track_name': str,
      'fastest_lap_time': str,
      'fastest_lap_psn': str,
      'entries': [ {driver, team, vehicle, livery, grid_number,
                    penalty_sec, penalty_pts, race_time_final,
                    base_points, fl_flag, podium_bonus,
                    rare_vehicle_bonus, vehicle_loyalty_bonus, points_total,
                    finish_pos, status} ]
    }
    Gibt None zurück wenn das Blatt leer/unvollständig ist.
    """

    def r(row_idx, col_idx):
        try:
            return str(rows[row_idx][col_idx]).strip()
        except (IndexError, TypeError):
            return ""

    # Zeile 3 (Index 2): Datum E3, Schnellste Runde G3, Fahrer I3
    # Zeile 2 (Index 1): Strecke E2 (merged E2:K2)
    try:
        track_name    = r(1, 3)   # E2 (Spalte-Index 3 = D, aber Sheet-Cols sind 0-basiert)
        race_date_str = r(2, 4)   # E3
        fastest_lap   = r(2, 6)   # G3
        fastest_lap_driver = r(2, 8)  # I3
    except Exception:
        return None

    if not track_name and not race_date_str:
        return None

    # Datum parsen: DD.MM.YYYY
    race_date = None
    if race_date_str:
        try:
            race_date = datetime.strptime(race_date_str, "%d.%m.%Y").date()
        except ValueError:
            log.warning(f"  Datum konnte nicht geparst werden: '{race_date_str}'")

    # Schnellste Runde in Sekunden (für Rating-Berechnung)
    fl_seconds = parse_time_to_seconds(fastest_lap.replace(".", ",").replace(",", ","))
    # Sheet nutzt Komma als Dezimaltrenner: '1:52,941'
    fl_seconds = parse_time_to_seconds(fastest_lap)

    entries = []
    # Daten ab Zeile 7 (Index 6)
    for row in rows[6:]:
        pos_raw = cell(row, 1)
        if not pos_raw or not pos_raw.isdigit():
            continue  # Leerzeile oder Kopfzeile

        finish_pos    = int(pos_raw)
        psn_name      = cell(row, 3)
        team_name     = cell(row, 4)
        vehicle_name  = cell(row, 5)
        livery_raw    = cell(row, 6)
        grid_raw      = cell(row, 7)
        penalty_raw   = cell(row, 8)
        penalty_pts   = int(cell(row, 9) or 0)
        race_time_raw = cell(row, 10)
        points_raw    = cell(row, 12)
        car_bonus_raw = cell(row, 13)
        points_total  = int(cell(row, 14) or 0)

        if not psn_name:
            continue

        # Status
        is_dnf = (race_time_raw == DNF_TIME or race_time_raw.startswith("8:00:00"))
        status = "DNF" if is_dnf else "FIN"

        # Renndauer in Sekunden (ohne Strafe)
        race_time_sec = parse_time_to_seconds(race_time_raw) if not is_dnf else None

        # Rating = RaceTime(ohne Strafe) / FastestLap
        # Hinweis: race_time_final enthält bereits Strafe;
        # race_time_raw = Endzeit mit Strafe laut Beschreibung (Spalte K = final)
        # Rating wird über Zeit-ohne-Strafe berechnet:
        penalty_sec = parse_penalty_seconds(penalty_raw)
        race_time_no_penalty_sec = None
        if race_time_sec is not None and penalty_sec:
            race_time_no_penalty_sec = race_time_sec - penalty_sec
        elif race_time_sec is not None:
            race_time_no_penalty_sec = race_time_sec

        rating = None
        if race_time_no_penalty_sec and fl_seconds:
            rating = round(race_time_no_penalty_sec / fl_seconds, 4)

        # Punkte parsen
        base_pts, fl_flag, podium_bonus = parse_base_points(points_raw)
        rare_bonus, loyalty_bonus = parse_car_bonus(car_bonus_raw)

        # Livery-Code (nur Grid-Nummer ist relevant für Lookup)
        grid_number = grid_raw  # '1', '2', '3' etc.

        entries.append({
            "finish_pos":           finish_pos,
            "psn_name":             psn_name,
            "team_name":            team_name,
            "vehicle_name":         vehicle_name,
            "livery_code":          livery_raw,
            "grid_number":          grid_number,
            "penalty_sec":          penalty_sec,
            "penalty_pts":          penalty_pts,
            "race_time_final":      race_time_raw if not is_dnf else None,
            "race_time_no_penalty": race_time_no_penalty_sec,
            "rating":               rating,
            "base_points":          base_pts,
            "fl_flag":              fl_flag,
            "podium_bonus":         podium_bonus,
            "rare_bonus":           rare_bonus,
            "loyalty_bonus":        loyalty_bonus,
            "points_total":         points_total,
            "status":               status,
        })

    if not entries:
        return None

    return {
        "race_date":          race_date,
        "track_name":         track_name,
        "fastest_lap_time":   fastest_lap,
        "fastest_lap_psn":    fastest_lap_driver,
        "fl_seconds":         fl_seconds,
        "entries":            entries,
    }


# ── DB-Import ─────────────────────────────────────────────────────────────────

def import_race(cur, season_id: int, race_number: int, data: dict):
    race_id = lookup_race(cur, season_id, race_number)
    if not race_id:
        log.warning(f"  Rennen {race_number} (season {season_id}) nicht in DB – übersprungen.")
        log.warning(f"  Bitte Rennen zuerst in der 'races'-Tabelle anlegen.")
        return

    log.info(f"  race_id={race_id}, {len(data['entries'])} Fahrer")

    # Fastest-Lap-Fahrer-ID für races-Update
    fl_driver_id = None
    if data["fastest_lap_psn"]:
        fl_driver_id = lookup_driver(cur, data["fastest_lap_psn"])

    # races-Tabelle updaten (Datum, Fastest Lap)
    cur.execute(
        """UPDATE races SET
             fastest_lap_time = %s,
             fastest_lap_driver_id = %s
           WHERE race_id = %s""",
        (data["fastest_lap_time"], fl_driver_id, race_id),
    )

    # Bestehende Ergebnisse dieses Rennens löschen (clean upsert)
    cur.execute("DELETE FROM bonus_points WHERE result_id IN "
                "(SELECT result_id FROM race_results WHERE race_id = %s)", (race_id,))
    cur.execute("DELETE FROM race_results WHERE race_id = %s", (race_id,))

    for entry in data["entries"]:
        psn   = entry["psn_name"]
        d_id  = lookup_or_create_driver(cur, psn)
        t_id  = lookup_team(cur, entry["team_name"])
        v_id  = lookup_vehicle(cur, entry["vehicle_name"])

        # Grid-ID: grid_number aus Sheet (1/2/3)
        g_id = lookup_grid(cur, race_id, entry["grid_number"])
        if not g_id:
            log.warning(f"  Grid {entry['grid_number']} für race_id={race_id} nicht gefunden")

        bonus_total = (entry["fl_flag"] +        # FL-Bonus-Wert wird aus bonus_fastest_lap gezählt
                       entry["podium_bonus"] +
                       entry["rare_bonus"] +
                       entry["loyalty_bonus"])

        cur.execute(
            """INSERT INTO race_results
               (race_id, grid_id, driver_id, vehicle_id, team_id,
                finish_pos_overall, race_time, race_time_final,
                time_percent, rating_at_race,
                points_base, bonus_total,
                bonus_podium, bonus_fastest_lap,
                bonus_rare_vehicle, bonus_vehicle_loyalty,
                points_total, status,
                penalty_seconds, penalty_points, livery_code)
               VALUES (%s,%s,%s,%s,%s,
                       %s,%s,%s,
                       %s,%s,
                       %s,%s,
                       %s,%s,
                       %s,%s,
                       %s,%s,
                       %s,%s,%s)""",
            (
                race_id, g_id, d_id, v_id, t_id,
                entry["finish_pos"],
                # race_time = Zeit ohne Strafe (als String), race_time_final = mit Strafe
                _seconds_to_timestr(entry["race_time_no_penalty"]),
                entry["race_time_final"],
                None,               # time_percent – optional, nicht im Sheet
                entry["rating"],
                entry["base_points"],
                bonus_total,
                entry["podium_bonus"],
                1 if entry["fl_flag"] else 0,
                entry["rare_bonus"],
                entry["loyalty_bonus"],
                entry["points_total"],
                entry["status"],
                entry["penalty_sec"],
                entry["penalty_pts"],
                entry["livery_code"] or None,
            ),
        )
        result_id = cur.lastrowid

        # Bonus-Einträge
        if entry["fl_flag"]:
            cur.execute(
                "INSERT INTO bonus_points (result_id, bonus_type, points) VALUES (%s,%s,%s)",
                (result_id, BONUS_FASTEST_LAP, 1),
            )
        if entry["podium_bonus"]:
            cur.execute(
                "INSERT INTO bonus_points (result_id, bonus_type, points) VALUES (%s,%s,%s)",
                (result_id, BONUS_PODIUM, entry["podium_bonus"]),
            )
        if entry["rare_bonus"]:
            cur.execute(
                "INSERT INTO bonus_points (result_id, bonus_type, points) VALUES (%s,%s,%s)",
                (result_id, BONUS_RARE_VEHICLE, entry["rare_bonus"]),
            )
        if entry["loyalty_bonus"]:
            cur.execute(
                "INSERT INTO bonus_points (result_id, bonus_type, points) VALUES (%s,%s,%s)",
                (result_id, BONUS_VEHICLE_LOYALTY, entry["loyalty_bonus"]),
            )

    log.info(f"  ✓ Rennen {race_number} importiert ({len(data['entries'])} Einträge)")


def _seconds_to_timestr(sec: float | None) -> str | None:
    """Konvertiert Sekunden zurück in H:MM:SS,mmm Format."""
    if sec is None:
        return None
    h = int(sec // 3600)
    m = int((sec % 3600) // 60)
    s = sec % 60
    ms = round((s - int(s)) * 1000)
    return f"{h}:{m:02d}:{int(s):02d},{ms:03d}"


# ── Hauptprogramm ─────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="RTC Sheet → DB Import")
    parser.add_argument("--season", type=int, default=None,
                        help="Season-ID (Standard: aktive Saison)")
    parser.add_argument("--race", type=int, default=None,
                        help="Nur dieses Rennen importieren (1–16)")
    args = parser.parse_args()

    db  = get_db()
    cur = db.cursor()

    try:
        # Saison ermitteln
        if args.season:
            cur.execute("SELECT season_id, name, sheet_id FROM seasons WHERE season_id = %s",
                        (args.season,))
        else:
            cur.execute("SELECT season_id, name, sheet_id FROM seasons WHERE is_active = 1")

        season = cur.fetchone()
        if not season:
            log.error("Keine passende Saison gefunden.")
            sys.exit(1)

        season_id = season["season_id"]
        sheet_id  = season["sheet_id"]
        log.info(f"Saison: {season['name']} (ID={season_id}), Sheet={sheet_id}")

        if not sheet_id:
            log.error("Keine sheet_id in der seasons-Tabelle eingetragen!")
            sys.exit(1)

        svc = get_sheets_service()

        # Verfügbare Tabs ermitteln
        tabs = list_sheet_tabs(svc, sheet_id)
        race_tabs = sorted(
            [t for t in tabs if t.isdigit()],
            key=lambda x: int(x)
        )
        log.info(f"Gefundene Rennen-Tabs: {race_tabs}")

        if args.race:
            race_tabs = [str(args.race)] if str(args.race) in race_tabs else []
            if not race_tabs:
                log.error(f"Tab '{args.race}' nicht im Sheet gefunden.")
                sys.exit(1)

        imported = 0
        skipped  = 0

        for tab in race_tabs:
            race_number = int(tab)
            log.info(f"── Verarbeite Tab '{tab}' (Rennen {race_number}) ──")

            rows = fetch_sheet(svc, sheet_id, tab)
            data = parse_race_sheet(rows)

            if not data:
                log.info(f"  Tab '{tab}' leer oder kein Ergebnis – übersprungen.")
                skipped += 1
                continue

            log.info(f"  Datum: {data['race_date']}, Strecke: {data['track_name']}")
            log.info(f"  Schnellste Runde: {data['fastest_lap_time']} ({data['fastest_lap_psn']})")

            import_race(cur, season_id, race_number, data)
            imported += 1

        db.commit()
        log.info(f"✓ Import abgeschlossen: {imported} Rennen importiert, {skipped} übersprungen.")

    except Exception as e:
        db.rollback()
        log.exception(f"Fehler beim Import: {e}")
        sys.exit(1)
    finally:
        cur.close()
        db.close()


if __name__ == "__main__":
    main()

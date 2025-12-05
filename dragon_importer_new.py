
"""
dragon_importer_new.py
----------------------
Self-contained importer for DRAGON workbooks (.xlsx) -> JTDS OBS model objects.

Expected "model" interface (your existing app provides this already):
  - model.unit_list        : lxml Element for <UnitList>
  - model.entcomp_list     : lxml Element for <EntityCompositionList>
  - Optional: model.scenario or a common ancestor element with namespace

We infer the XML namespace from model.unit_list.tag so this works in any JTDS ns.
"""

from __future__ import annotations
import re
import uuid
import random
import sys
from pathlib import Path
from typing import Optional, Dict, Any, Iterable, Set, Callable

import pandas as pd
from lxml import etree as ET

class DragonImportCancelled(Exception):
    """Raised when the caller cancels an in-progress DRAGON import."""


# ------------------------
# Utilities
# ------------------------
def _ns_and_tag_funcs(model) -> tuple[str, callable]:
    """Infer namespace from the UnitList element and build a jtag(name) helper."""
    unitlist = model.unit_list
    t = unitlist.tag
    if t.startswith("{") and "}" in t:
        ns = t[1:t.find("}")]
    else:
        ns = ""
    def jtag(name: str) -> str:
        return f"{{{ns}}}{name}" if ns else name
    return ns, jtag


def _pick_col(cols: Iterable[str], *candidates: str) -> Optional[str]:
    s = [str(c).strip() for c in cols]
    lowers = {c.lower(): c for c in s}
    for cand in candidates:
        k = cand.lower()
        if k in lowers:
            return lowers[k]
    # try looser contains
    for cand in candidates:
        k = cand.lower()
        for c in s:
            if k in c.lower():
                return c
    return None


def _norm(v: Any) -> str:
    if v is None:
        return ""
    if isinstance(v, float) and pd.isna(v):
        return ""
    return str(v).strip()


def _to_underscore(s: str) -> str:
    s = (s or "").upper()
    # "1 CO" -> "A CO"
    m = re.match(r'^\s*(\d+)\s*CO\b', s)
    if m:
        n = int(m.group(1))
        if 1 <= n <= 26:
            s = chr(64 + n) + " CO" + s[m.end():]
    s = re.sub(r'[^A-Z0-9]+', '_', s)
    s = re.sub(r'_+', '_', s).strip('_')
    return s


_ABBREV_MULTI = [
    ("OPERATIONAL_STRATEGIC_COMMAND", "OSC"),
]
_ABBREV_TOKEN = {
    "HEADQUARTERS": "HQ",
    "OPERATIONS": "OPS",
    "SECURITY": "SEC",
    "SECTION": "SEC",
    "GROUND_FORCES": "GND_FORCES",
    "BATTALION": "BN",
    "BRIGADE": "BDE",
    "REGIMENT": "REGT",
    "COMPANY": "CO",
    "BATTERY": "BTY",
    "PLATOON": "PLT",
    "SQUAD": "SQD",
}

def _apply_abbrev(s: str) -> str:
    if not s:
        return s
    u = s.upper()
    # Additional basic compressions
    u = u.replace('COMMAND', 'CMD')
    u = u.replace('SPECIAL', 'SPEC')
    u = u.replace('FIRE', 'FIR')
    # phase 1: multi-token
    for long, short in _ABBREV_MULTI:
        u = u.replace(long + "_SOUTH", short + "_SOUTH")
        u = u.replace(long, short)
    # phase 2: token-level
    tokens = u.split("_")
    tokens = [_ABBREV_TOKEN.get(tok, tok) for tok in tokens]
    # collapse repeats
    out = []
    for tok in tokens:
        if not out or out[-1] != tok:
            out.append(tok)
    return "_".join(out)

def _smart_join(base: str, suffix: str, max_tokens: int = 12) -> str:
    """Join base + suffix, removing duplicate tokens and capping length.
    Keeps order, removes consecutive duplicates and any suffix token that already
    appears within the last 3 tokens of base. Then trims to max_tokens from the left.
    """
    if not suffix:
        out = _apply_abbrev(base)
    else:
        bt = [t for t in _apply_abbrev(base).split('_') if t]
        st = [t for t in _apply_abbrev(suffix).split('_') if t]
        for tok in st:
            if not bt or tok != bt[-1]:
                # avoid re-adding if it appears in the last 3 tokens
                if tok not in bt[-3:]:
                    bt.append(tok)
        out = '_'.join(bt)
    # cap tokens
    toks = [t for t in out.split('_') if t]
    if len(toks) > max_tokens:
        toks = toks[-max_tokens:]
    return '_'.join(toks)


def _parse_den_to_attrs(den: str) -> Dict[str, str]:
    """Parse a DIS enumeration cell like 'kind=1 domain=1 country=0 echelon=5 type=2 subtype=0 modifier=0'"""
    if not den:
        return {}
    out = {}
    for part in re.split(r"[;,]\s*|\s+", den.strip()):
        if "=" in part:
            k, v = part.split("=", 1)
            out[k.strip()] = v.strip()
    return out


def _lvc_make(existing: set[str], seed: str | None = None, prefix: str = "U", length: int = 10, use_seed: bool = True) -> str:
    if use_seed and seed:
        cleaned = re.sub(r"[^A-Z0-9]+", "", (seed or "").upper())
        if cleaned.startswith(prefix):
            cleaned = cleaned[len(prefix):]
        if len(cleaned) >= length:
            candidate = prefix + cleaned[:length]
            if candidate not in existing:
                existing.add(candidate)
                return candidate
    while True:
        candidate = prefix + uuid.uuid4().hex[:length].upper()
        if candidate not in existing:
            existing.add(candidate)
            return candidate

def _make_entity_xml_id(existing: set[str]) -> str:
    while True:
        candidate = f"ID_{random.randint(0, 9999999999):010d}"
        if candidate not in existing:
            existing.add(candidate)
            return candidate


def _infer_echelon(name: str) -> str:
    u = (name or "").upper()
    if "_BN" in u or " BATTALION" in u: return "Battalion"
    if "_BDE" in u or " BRIGADE" in u: return "Brigade"
    if "_REGT" in u or " REGIMENT" in u: return "Regiment"
    if "_CO" in u or " COMPANY" in u: return "Company"
    if "BTRY" in u or "_BTY" in u: return "Battery"
    if "_PLT" in u or " PLATOON" in u: return "Platoon"
    if "_SEC" in u or " SECTION" in u: return "Section"
    if "_SQD" in u or " SQUAD" in u: return "Squad"
    return "Other"



ECHELON_ABBREV_MAP = {
    'TM': 'Team',
    'TEAM': 'Team',
    'SEC': 'Section',
    'SECTION': 'Section',
    'PLT': 'Platoon',
    'PLATOON': 'Platoon',
    'CO': 'Company',
    'COMPANY': 'Company',
    'BN': 'Battalion',
    'BATTALION': 'Battalion',
    'BDE': 'Brigade',
    'BRIGADE': 'Brigade',
    'BTY': 'Battery',
    'BATTERY': 'Battery',
    'DIV': 'Division',
    'DIVISION': 'Division',
    'ARMY': 'Army',
    'CORPS': 'Corps',
    'COMMAND': 'Command',
    'CMD': 'Command',
    'SQD': 'Squad',
    'SQUAD': 'Squad'
}


def _expand_echelon_name(value: str) -> str:
    if not value:
        return value
    key = value.strip().upper()
    return ECHELON_ABBREV_MAP.get(key, value.strip())

# ------------------------
# Importer
# ------------------------
def import_dragon_enhanced(
    model,
    xlsx_path: str,
    allowed_uids: Optional[Set[str]] = None,
    *,
    progress_cb: Optional[Callable[[str, float], None]] = None,
    cancel_cb: Optional[Callable[[], bool]] = None,
) -> int:
    """
    Reads a DRAGON workbook and builds Units + EntityCompositions in the JTDS model.
    - UNIT INFO creates top-level Units
    - Each row's TEMPLATE NAME sheet (if present) adds subordinate Units + equipment/personnel
    - Names are underscore-normalized, abbreviated, and suffixed with <=2 ancestors
    When allowed_uids is provided, only UNIT INFO rows whose UID is in that set (case-insensitive) are processed.
    Returns total count of Units under UnitList after import (before flattening).
    """
    def _emit(message: str, fraction: float) -> None:
        if not progress_cb:
            return
        try:
            progress_cb(message, max(0.0, min(fraction, 1.0)))
        except Exception:
            pass

    def _check_cancel() -> None:
        if cancel_cb and cancel_cb():
            raise DragonImportCancelled()

    ns, jtag = _ns_and_tag_funcs(model)
    unitlist = model.unit_list
    entlist  = model.entcomp_list

    _emit("Opening DRAGON workbook...", 0.05)
    _check_cancel()
    xls = pd.ExcelFile(xlsx_path)
    if "UNIT INFO" not in xls.sheet_names:
        raise ValueError("UNIT INFO sheet not found in DRAGON workbook.")
    ui = xls.parse("UNIT INFO")
    ui.columns = [str(c).strip() for c in ui.columns]

    allowed_set: Optional[Set[str]] = None
    if allowed_uids:
        allowed_set = {str(uid).strip().upper() for uid in allowed_uids if str(uid).strip()}

    def _uid_included(uid_value: str) -> bool:
        if allowed_set is None:
            return True
        norm = (uid_value or '').strip().upper()
        return bool(norm) and norm in allowed_set


    col_uid    = _pick_col(ui.columns, "UID", "UNIT UID", "ID")
    col_puid   = _pick_col(ui.columns, "PARENT UID", "PARENT", "PARENT ID")
    col_name   = _pick_col(ui.columns, "UNIT", "UNIT NAME", "NAME", "UNIT TITLE", "DISPLAY NAME")
    col_uclass = _pick_col(ui.columns, "UNIT CLASS", "AGGREGATE NAME", "CLASS")
    col_tname  = _pick_col(ui.columns, "TYPE NAME", "TYPENAME")
    col_2525   = _pick_col(ui.columns, "2525C", "MILSTD2525C", "MILSTD 2525C")
    col_echelon = _pick_col(ui.columns, "ECHELON", "ECH", "ECHELON NAME")
    col_den    = _pick_col(ui.columns, "DIS ENUMERATION", "DIS_ENUMERATION", "DIS ENUM", "DIS")
    col_templ  = _pick_col(ui.columns, "TEMPLATE NAME", "TEMPLATE", "SHEET", "STRUCTURE SHEET")

    total_rows = max(1, len(ui))
    template_ref_count = 0
    if col_templ and col_uid:
        for _, r in ui.iterrows():
            _check_cancel()
            templ_name = _norm(r.get(col_templ)) if col_templ else ""
            if not templ_name or templ_name not in xls.sheet_names:
                continue
            uid_value = _norm(r.get(col_uid)) if col_uid else ""
            if _uid_included(uid_value):
                template_ref_count += 1
        template_ref_count = max(template_ref_count, 1)
    else:
        template_ref_count = 1

    unitclass_by_code: Dict[str, str] = {}
    unitclass_list = model.classdata.find(jtag("UnitClassList"))
    if unitclass_list is not None:
        for uc in unitclass_list.findall('.//' + jtag("UnitClass")):
            code = (uc.findtext(jtag("MilStd2525CCode")) or '').strip()
            name = (uc.findtext(jtag("Name")) or '').strip()
            if code and name and code.upper() not in unitclass_by_code:
                unitclass_by_code[code.upper()] = name


    by_uid: Dict[str, ET.Element] = {}
    used_names_by_parent: Dict[int | None, Dict[str, ET.Element]] = {}
    seeded_parents: Set[int | None] = set()
    new_units: Set[int] = set()
    global_names: Dict[str, ET.Element] = {}
    global_seeded = False
    used_lvc:   set[str] = set()
    used_entity_ids: Set[str] = set()
    for node in unitlist.findall('.//' + jtag('LvcId')):
        if node.text:
            used_lvc.add(node.text.strip().upper())
    for node in entlist.findall('.//' + jtag('LvcId')):
        if node.text:
            used_lvc.add(node.text.strip().upper())
    for ec in entlist.findall(jtag('EntityComposition')):
        attr = ec.get('id')
        if attr:
            used_entity_ids.add(attr.strip())

    # ---- helpers inside importer
    def _apply_unit_metadata(node: ET.Element, class_name: str = "", ms2525: str = "", den: str = "", echelon: str = "") -> None:
        if node is None:
            return
        ms_value = (ms2525 or '').strip().upper()
        if class_name:
            class_el = node.find(jtag('ClassName'))
            if class_el is None:
                class_el = ET.SubElement(node, jtag('ClassName'))
            class_el.text = class_name
        if ms_value:
            code_el = node.find(jtag('MilStd2525CCode'))
            if code_el is None:
                code_el = ET.SubElement(node, jtag('MilStd2525CCode'))
            code_el.text = ms_value
        attrs = _parse_den_to_attrs(den or '')
        if attrs:
            ude = node.find(jtag('UnitDisEnumeration'))
            if ude is None:
                ude = ET.SubElement(node, jtag('UnitDisEnumeration'))
            for k, v in attrs.items():
                if v:
                    ude.set(k, v)
        ech_text = echelon or ''
        ech_value = _expand_echelon_name(ech_text) if ech_text else ''
        if ech_value:
            ech_el = node.find(jtag('Echelon'))
            if ech_el is None:
                ech_el = ET.SubElement(node, jtag('Echelon'))
            ech_el.text = ech_value

    def _ensure_unit(uid: str, display: str, uclass: str, ms2525: str, den: str, echelon: str) -> ET.Element:
        key = (uid or display or "").strip()
        ms_val = (ms2525 or '').strip().upper()
        class_name = ''
        if ms_val and ms_val in unitclass_by_code:
            class_name = unitclass_by_code[ms_val]
        elif uclass:
            class_name = uclass
        if key in by_uid:
            existing = by_uid[key]
            _apply_unit_metadata(existing, class_name, ms_val, den, echelon)
            return existing
        base = _apply_abbrev(_to_underscore(display or uid or "UNIT"))
        u = ET.SubElement(unitlist, jtag("Unit"))
        new_units.add(id(u))
        # essential fields
        ET.SubElement(u, jtag("LvcId")).text = _lvc_make(used_lvc, prefix="U", use_seed=False)
        name_el = ET.SubElement(u, jtag("Name")); name_el.text = base
        _apply_unit_metadata(u, class_name, ms_val, den, echelon)
        # default OwningFederate
        ow = ET.SubElement(u, jtag("OwningFederate"))
        ET.SubElement(ow, jtag("Federate")).text = "WARSIM"
        # remember base for suffixing later
        u.set("dataBase", base)
        by_uid[key] = u
        return u

    # Top-level units
    _emit("Generating top-level units...", 0.1)
    top_processed = 0
    for _, r in ui.iterrows():
        _check_cancel()
        uid = _norm(r.get(col_uid)) if col_uid else ""
        if not _uid_included(uid):
            continue
        name = _norm(r.get(col_name))
        ucls = _norm(r.get(col_uclass))
        ms = _norm(r.get(col_2525))
        ech = _norm(r.get(col_echelon)) if col_echelon else ''
        den = _norm(r.get(col_den))
        _ensure_unit(uid, name, ucls, ms, den, ech)
        top_processed += 1
        frac = 0.1 + min(top_processed / total_rows, 1.0) * 0.05
        _emit("Generating top-level units...", frac)

    # Parent-child mapping; we keep it nested *temporarily*
    _emit("Linking unit hierarchy...", 0.16)
    hierarchy_processed = 0
    for _, r in ui.iterrows():
        _check_cancel()
        uid = _norm(r.get(col_uid)) if col_uid else ""
        if not _uid_included(uid):
            continue
        puid = _norm(r.get(col_puid)) if col_puid else ""
        if uid and puid and uid in by_uid and puid in by_uid:
            child = by_uid[uid]
            parent = by_uid[puid]
            if child.getparent() is not None and child.getparent() is not unitlist:
                try:
                    child.getparent().remove(child)
                except Exception:
                    pass
            parent.append(child)
        hierarchy_processed += 1
        frac = 0.16 + min(hierarchy_processed / total_rows, 1.0) * 0.04
        _emit("Linking unit hierarchy...", frac)

    def _suffix_to_ancestors(parent_node, max_levels: int = 2) -> str:
        parts = []
        cur = parent_node
        while cur is not None and len(parts) < max_levels:
            if not str(getattr(cur, "tag", "")).endswith("Unit"):
                break
            dn = cur.get("dataBase") or (cur.findtext(jtag("Name")) or cur.findtext(jtag("DisplayName")) or "")
            dn = _apply_abbrev(_to_underscore(dn))
            if dn:
                parts.append(dn)
            cur = cur.getparent() if hasattr(cur, "getparent") else None
        return "_".join(parts)


    def _seed_global_names() -> None:
        nonlocal global_seeded
        if global_seeded:
            return
        global_seeded = True
        for existing in unitlist.findall('.//' + jtag('Unit')):
            if id(existing) in new_units:
                continue
            existing_name = (existing.findtext(jtag('Name')) or '').strip()
            if not existing_name:
                continue
            key = existing_name.upper()
            if key not in global_names:
                global_names[key] = existing

    def _finalize_name(node: ET.Element):
        parent = node.getparent() if hasattr(node, "getparent") else None
        parent_key = id(parent) if parent is not None else None
        names_for_parent = used_names_by_parent.setdefault(parent_key, {})
        _seed_global_names()
        if parent_key not in seeded_parents:
            seeded_parents.add(parent_key)
            if parent is not None:
                for sibling in parent:
                    if sibling is node or not str(getattr(sibling, "tag", "")).endswith("Unit"):
                        continue
                    if id(sibling) in new_units:
                        continue
                    sib_name = (sibling.findtext(jtag("Name")) or "").strip()
                    if sib_name:
                        key = sib_name.upper()
                        names_for_parent.setdefault(key, sibling)
                        global_names.setdefault(key, sibling)
        current = (node.findtext(jtag("Name")) or "").strip().upper()
        if current and names_for_parent.get(current) is node:
            del names_for_parent[current]
        for key, val in list(global_names.items()):
            if val is node:
                del global_names[key]
        base = node.get("dataBase") or (node.findtext(jtag("Name")) or "").strip() or "UNIT"
        suffix = _suffix_to_ancestors(parent, 2) if parent is not None else ""
        cand = _smart_join(base, suffix, max_tokens=10)
        candidate = cand
        suffix_index = 2
        while True:
            up = candidate.upper()
            conflict_parent = names_for_parent.get(up)
            conflict_global = global_names.get(up)
            if (conflict_parent is not None and conflict_parent is not node) or (conflict_global is not None and conflict_global is not node):
                candidate = f"{cand}_{suffix_index}"
                suffix_index += 1
                continue
            break
        node.find(jtag("Name")).text = candidate
        up = candidate.upper()
        names_for_parent[up] = node
        global_names[up] = node
    # ---- Template sheets
    _emit("Processing template sheets...", 0.2)
    template_processed = 0
    for _, r in ui.iterrows():
        _check_cancel()
        templ = _norm(r.get(col_templ)) if col_templ else ""
        if not templ or templ not in xls.sheet_names:
            continue
        uid = _norm(r.get(col_uid)) if col_uid else ""
        if not _uid_included(uid):
            continue
        top = by_uid.get(uid)
        if top is None:
            continue

        df = xls.parse(templ)
        df.columns = [str(c).strip() for c in df.columns]

        c_uid    = _pick_col(df.columns, "UID", "UNIT UID", "ID")
        c_puid   = _pick_col(df.columns, "PARENT UID", "PARENT", "PARENT ID")
        c_name   = _pick_col(df.columns, "UNIT", "NAME", "DISPLAY NAME", "UNIT NAME")
        c_group  = _pick_col(df.columns, "TYPE GROUP", "GROUP")
        c_ecc    = _pick_col(df.columns, "EQUIPMENT", "ECC", "COMPOSITION", "ENTITY COMPOSITION", "EQUIPMENT TYPE")
        c_qty    = _pick_col(df.columns, "QTY", "QUANTITY", "COUNT", "#")
        c_uclass = _pick_col(df.columns, "UNIT CLASS", "AGGREGATE NAME", "CLASS")
        c_2525   = _pick_col(df.columns, "2525C", "MILSTD2525C", "MILSTD 2525C")
        c_den    = _pick_col(df.columns, "DIS ENUMERATION", "DIS_ENUMERATION", "DIS ENUM", "DIS")
        c_echelon = _pick_col(df.columns, "ECHELON", "ECH", "ECHELON NAME")
        c_crew   = _pick_col(df.columns, "PERSONNEL TYPE", "CREW TYPE", "PERSONNEL")

        uid_to_parent: Dict[str, str] = {}
        if c_uid:
            for _, rr in df.iterrows():
                ru = _norm(rr.get(c_uid))
                if not ru:
                    continue
                rp = _norm(rr.get(c_puid)) if c_puid else ""
                uid_to_parent[ru] = rp
        sub_by_uid: Dict[str, ET.Element] = {}
        uid_to_node: Dict[str, ET.Element] = {}
        if uid:
            uid_to_node[uid] = top
            sub_by_uid.setdefault(uid, top)

        def _resolve_target_unit(start_uid: str) -> ET.Element:
            current = (start_uid or "").strip()
            visited: Set[str] = set()
            while current:
                node = uid_to_node.get(current)
                if node is not None:
                    return node
                if current in visited:
                    break
                visited.add(current)
                nxt = uid_to_parent.get(current)
                if not nxt or nxt == current:
                    break
                current = nxt
            return top

        root_consumed = False
        # Create subordinate Units (temporarily nested under 'top')
        for _, rr in df.iterrows():
            _check_cancel()
            tg = _norm(rr.get(c_group)).upper() if c_group else ""
            if tg != "UNIT":
                continue
            suid  = _norm(rr.get(c_uid)) if c_uid else ""
            sname = _norm(rr.get(c_name))
            scls  = _norm(rr.get(c_uclass))
            s2525 = _norm(rr.get(c_2525)) if c_2525 else ''
            sden  = _norm(rr.get(c_den)) if c_den else ''
            sech  = _norm(rr.get(c_echelon)) if c_echelon else ''
            ms_val = (s2525 or '').strip().upper()
            class_name = unitclass_by_code.get(ms_val, '') if ms_val else ''
            if not class_name:
                class_name = scls
            is_root_candidate = not root_consumed
            if suid and suid == uid:
                is_root_candidate = True
            if suid:
                existing = uid_to_node.get(suid)
                if existing is not None:
                    sub_by_uid.setdefault(suid, existing)
                    _apply_unit_metadata(existing, class_name or '', ms_val, sden, sech)
                    if not root_consumed and is_root_candidate:
                        root_consumed = True
                    continue
            if is_root_candidate:
                _apply_unit_metadata(top, class_name or '', ms_val, sden, sech)
                if suid:
                    sub_by_uid[suid] = top
                    uid_to_node[suid] = top
                root_consumed = True
                continue
            base  = _apply_abbrev(_to_underscore(sname or suid or "UNIT"))
            node  = ET.SubElement(top, jtag("Unit"))
            new_units.add(id(node))
            ET.SubElement(node, jtag("LvcId")).text = _lvc_make(used_lvc, prefix="U", use_seed=False)
            ET.SubElement(node, jtag("Name")).text  = base
            node.set("dataBase", base)
            _apply_unit_metadata(node, class_name or '', ms_val, sden, sech)
            ow = ET.SubElement(node, jtag("OwningFederate"))
            ET.SubElement(ow, jtag("Federate")).text = "WARSIM"
            if suid:
                sub_by_uid[suid] = node
                uid_to_node[suid] = node

        # Re-parent subordinate units per PARENT UID
        for _, rr in df.iterrows():
            _check_cancel()
            tg = _norm(rr.get(c_group)).upper() if c_group else ""
            if tg != "UNIT":
                continue
            suid = _norm(rr.get(c_uid)) if c_uid else ""
            puid = _norm(rr.get(c_puid)) if c_puid else ""
            if suid and puid:
                child  = sub_by_uid.get(suid)
                parent = sub_by_uid.get(puid)
                if parent is None:
                    parent = top
                if child is not None and parent is not None:
                    if child.getparent() is not parent:
                        try:
                            child.getparent().remove(child)
                        except Exception:
                            pass
                        parent.append(child)

        # Equipment (+ optional crew) -> EntityComposition
        for _, rr in df.iterrows():
            _check_cancel()
            tg = _norm(rr.get(c_group)).upper() if c_group else ""
            if tg != "EQUIPMENT":
                continue
            target_uid = _norm(rr.get(c_puid)) if c_puid else ""
            eq_uid = _norm(rr.get(c_uid)) if c_uid else ""
            eq_name = _norm(rr.get(c_ecc))
            qty     = _norm(rr.get(c_qty))
            crew    = _norm(rr.get(c_crew))
            target_node = _resolve_target_unit(target_uid) if target_uid else top
            if eq_uid and eq_uid not in uid_to_node:
                uid_to_node[eq_uid] = target_node
            item_name = _norm(rr.get(c_name)) if c_name else ''
            class_name = item_name or eq_name
            sup_lvc = target_node.findtext(jtag("LvcId"))
            if not sup_lvc:
                sup_lvc = _lvc_make(used_lvc, prefix="U", use_seed=False)
                lid_el = target_node.find(jtag("LvcId"))
                if lid_el is None:
                    lid_el = ET.SubElement(target_node, jtag("LvcId"))
                lid_el.text = sup_lvc
            ec = ET.SubElement(entlist, jtag("EntityComposition"))
            ec.set('id', _make_entity_xml_id(used_entity_ids))
            ET.SubElement(ec, jtag("LvcId")).text = _lvc_make(used_lvc, prefix="U", use_seed=False)
            role_base = _to_underscore((class_name or eq_name or "EQUIPMENT"))
            role = role_base + '_' + (_to_underscore(target_node.findtext(jtag('Name')) or ''))
            ET.SubElement(ec, jtag("Role")).text = role
            ET.SubElement(ec, jtag("UnitSuperior")).text = sup_lvc
            ET.SubElement(ec, jtag("ClassName")).text = class_name or "UNKNOWN"
            if qty and qty.isdigit():
                ET.SubElement(ec, jtag("Quantity")).text = str(int(qty))
            if crew:
                cl = ET.SubElement(ec, jtag("CrewList")); cr = ET.SubElement(cl, jtag("Crew"))
                ET.SubElement(cr, jtag("ClassName")).text = crew
            ow = ET.SubElement(ec, jtag("OwningFederate")); ET.SubElement(ow, jtag("Federate")).text = "WARSIM"

        # Personnel-only rows -> separate compositions
        for _, rr in df.iterrows():
            _check_cancel()
            tg = _norm(rr.get(c_group)).upper() if c_group else ""
            if tg != "PERSONNEL":
                continue
            target_uid = _norm(rr.get(c_puid)) if c_puid else ""
            crew = _norm(rr.get(c_crew)) if c_crew else ''
            per_uid = _norm(rr.get(c_uid)) if c_uid else ""
            target_node = _resolve_target_unit(target_uid) if target_uid else top
            if per_uid and per_uid not in uid_to_node:
                uid_to_node[per_uid] = target_node
            item_name = _norm(rr.get(c_name)) if c_name else ''
            class_name = item_name or crew or 'Personnel'
            sup_lvc = target_node.findtext(jtag("LvcId"))
            if not sup_lvc:
                sup_lvc = _lvc_make(used_lvc, prefix="U", use_seed=False)
                lid_el = target_node.find(jtag("LvcId"))
                if lid_el is None:
                    lid_el = ET.SubElement(target_node, jtag("LvcId"))
                lid_el.text = sup_lvc
            ec = ET.SubElement(entlist, jtag("EntityComposition"))
            ec.set('id', _make_entity_xml_id(used_entity_ids))
            ET.SubElement(ec, jtag("LvcId")).text = _lvc_make(used_lvc, prefix="U", use_seed=False)
            role = _to_underscore(class_name or 'Personnel') + '_' + (_to_underscore(target_node.findtext(jtag('Name')) or ''))
            ET.SubElement(ec, jtag("Role")).text = role
            ET.SubElement(ec, jtag("UnitSuperior")).text = sup_lvc
            ET.SubElement(ec, jtag("ClassName")).text = class_name
            ow = ET.SubElement(ec, jtag("OwningFederate")); ET.SubElement(ow, jtag("Federate")).text = "WARSIM"
        # Finalize names for new sub units
        for n in sub_by_uid.values():
            _check_cancel()
            _finalize_name(n)

        template_processed += 1
        frac = 0.2 + min(template_processed / template_ref_count, 1.0) * 0.65
        _emit(
            f"Processing template sheets ({template_processed}/{template_ref_count})...",
            min(frac, 0.85),
        )

    # Finalize names for top-level as well
    _emit("Finalizing unit names and roles...", 0.9)
    for u in list(unitlist):
        _check_cancel()
        _finalize_name(u)

    _dedupe_entity_roles(entlist, jtag)
    for ec in entlist.findall(jtag('EntityComposition')):
        if not (ec.get('id')):
            ec.set('id', _make_entity_xml_id(used_entity_ids))
    _emit("DRAGON workbook processed", 1.0)
    return len(list(unitlist))



def _default_unitclass_master_path() -> Path:
    """Locate the default UnitClass master workbook bundled with the application."""
    candidates: list[Path] = []
    meipass = getattr(sys, '_MEIPASS', None)
    if meipass:
        try:
            candidates.append(Path(meipass))
        except Exception:
            pass
    module_file = globals().get('__file__')
    if module_file:
        try:
            candidates.append(Path(module_file).resolve().parent)
        except Exception:
            pass
    candidates.append(Path.cwd())
    examined: set[Path] = set()
    for base in candidates:
        if not isinstance(base, Path):
            base = Path(base)
        if base in examined:
            continue
        examined.add(base)
        candidate = base / 'UnitClass-Masters' / 'unitclass-master.xlsx'
        if candidate.exists():
            return candidate
    base = candidates[0] if candidates else Path.cwd()
    if not isinstance(base, Path):
        base = Path(base)
    return base / 'UnitClass-Masters' / 'unitclass-master.xlsx'


def append_unitclasses_to_master(dragon_xlsx_path: str, master_path: str | Path | None = None) -> int:
    """Append new UnitClass entries from a DRAGON workbook when their UNIT CLASS is not already in the master."""
    if not dragon_xlsx_path:
        raise ValueError('DRAGON workbook path is required.')
    dragon_file = Path(dragon_xlsx_path).expanduser()
    if not dragon_file.exists():
        raise FileNotFoundError(f'DRAGON workbook not found: {dragon_file}')
    if master_path is None:
        master_file = _default_unitclass_master_path()
    else:
        master_file = Path(master_path).expanduser()
        if master_file.is_dir():
            master_file = master_file / 'unitclass-master.xlsx'
    if not master_file.exists():
        raise FileNotFoundError(f'UnitClass master not found: {master_file}')

    def _norm_name_key(name: str) -> str:
        return ' '.join(_norm(name).upper().split()) if name else ''

    try:
        xls = pd.ExcelFile(dragon_file)
    except Exception as exc:
        raise ValueError(f'Failed to open DRAGON workbook: {exc}') from exc

    try:
        master_df = pd.read_excel(master_file)
    except FileNotFoundError:
        master_df = pd.DataFrame(columns=['UNIT CLASS', 'TYPE NAME', '2525C'])
    except Exception as exc:
        raise ValueError(f'Failed to read UnitClass master: {exc}') from exc

    if not list(master_df.columns):
        master_df = pd.DataFrame(columns=['UNIT CLASS', 'TYPE NAME', '2525C'])
    master_df = master_df.rename(columns=lambda c: str(c).strip().upper() if isinstance(c, str) else c)
    for col in ('UNIT CLASS', 'TYPE NAME', '2525C'):
        if col not in master_df.columns:
            master_df[col] = ''

    master_df['UNIT CLASS'] = master_df['UNIT CLASS'].map(_norm)
    master_df['TYPE NAME'] = master_df['TYPE NAME'].map(_norm)
    master_df['2525C'] = master_df['2525C'].map(lambda v: _norm(v).upper().replace(' ', ''))

    preferred = ['UNIT CLASS', 'TYPE NAME', '2525C']
    ordered_cols = preferred + [c for c in master_df.columns if c not in preferred]
    master_df = master_df[ordered_cols]

    existing_names: set[str] = set()
    keep_rows: list[bool] = []
    for val in master_df['UNIT CLASS']:
        key = _norm_name_key(val)
        if not key or key in existing_names:
            keep_rows.append(False)
        else:
            keep_rows.append(True)
            existing_names.add(key)
    master_df = master_df.loc[keep_rows].reset_index(drop=True)

    template = {col: '' for col in master_df.columns}
    added_rows: list[dict[str, str]] = []

    for sheet_name in xls.sheet_names:
        try:
            df = xls.parse(sheet_name)
        except Exception:
            continue
        if df.empty:
            continue
        df.columns = [str(c).strip() for c in df.columns]
        col_uclass = _pick_col(df.columns, 'UNIT CLASS', 'AGGREGATE NAME', 'CLASS')
        col_code = _pick_col(df.columns, '2525C', 'MILSTD2525C', 'MILSTD 2525C')
        col_tname = _pick_col(df.columns, 'TYPE NAME', 'TYPENAME')
        if not col_uclass or not col_code:
            continue
        for _, row in df.iterrows():
            cname_raw = _norm(row.get(col_uclass))
            code_raw = _norm(row.get(col_code))
            tname_raw = _norm(row.get(col_tname)) if col_tname else ''
            key = _norm_name_key(cname_raw)
            if not key or not code_raw:
                continue
            if key in existing_names:
                continue
            existing_names.add(key)
            row_dict = template.copy()
            row_dict['UNIT CLASS'] = cname_raw
            row_dict['2525C'] = code_raw.upper().replace(' ', '') if code_raw else ''
            if tname_raw:
                row_dict['TYPE NAME'] = tname_raw
            added_rows.append(row_dict)

    if added_rows:
        master_df = pd.concat([master_df, pd.DataFrame(added_rows)], ignore_index=True)

    try:
        master_df.to_excel(master_file, index=False)
    except Exception as exc:
        raise ValueError(f'Failed to write UnitClass master: {exc}') from exc

    return len(added_rows)





def _dedupe_entity_roles(entlist, jtag):
    seen: dict[str, int] = {}
    for ec in entlist.findall(jtag('EntityComposition')):
        role = ec.find(jtag('Role'))
        if role is None or not (role.text or "").strip():
            continue
        key = role.text.strip()
        count = seen.get(key, 0) + 1
        seen[key] = count
        if count > 1:
            role.text = f"{count - 1}_{key}"


# ------------------------
# Normalization to JTDS
# ------------------------
def normalize_to_jtds_schema(model) -> None:
    """
    Ensure JTDS-compliant structure:
     - Units have LvcId/Name/ClassName, common flags, OwningFederate, MtwsData
     - Personnel under Units -> EntityCompositions
     - Flatten nested Units; link with UnitSuperior
     - Strip helper @dataBase attributes
    """
    ns, j = _ns_and_tag_funcs(model)
    unitlist = model.unit_list
    entlist  = model.entcomp_list

    # ---- Ensure fields on Units; convert inline refs (if any) and Personnel
    used_e = set((e.text or '').strip().upper() for e in entlist.findall(".//" + j("LvcId")) if e.text)
    used_u = set((e.text or '').strip().upper() for e in unitlist.findall(".//" + j("LvcId")) if e.text)
    used_entity_ids = set((ec.get('id') or '').strip() for ec in entlist.findall(j("EntityComposition")) if ec.get('id'))

    def new_e():
        return _lvc_make(used_e, prefix="U", use_seed=False)

    def new_entity_id():
        return _make_entity_xml_id(used_entity_ids)

    for unit in unitlist.findall(".//" + j("Unit")):
        # Remove helper attribute
        try:
            unit.attrib.pop("dataBase", None)
        except Exception:
            pass

        # LvcId
        lvc = unit.find(j("LvcId"))
        if lvc is None:
            lvc = ET.SubElement(unit, j("LvcId"))
            lvc.text = _lvc_make(used_u, prefix="U", use_seed=False)
        else:
            existing = (lvc.text or "").strip()
            if existing:
                used_u.add(existing.upper())

        # Name
        nm = unit.find(j("Name"))
        if nm is None:
            nm = ET.SubElement(unit, j("Name"))
            nm.text = "UNIT"

        # ClassName default
        if unit.find(j("ClassName")) is None:
            ET.SubElement(unit, j("ClassName")).text = "UNKNOWN"

        # Echelon
        ech = unit.find(j("Echelon"))
        if ech is None:
            ech = ET.SubElement(unit, j("Echelon"))
            ech_value = _infer_echelon(nm.text or "")
            ech.text = _expand_echelon_name(ech_value)
        else:
            ech.text = _expand_echelon_name(ech.text or "")

        # OwningFederate/Federate=WARSIM
        ow = unit.find(j("OwningFederate")); 
        if ow is None: ow = ET.SubElement(unit, j("OwningFederate"))
        fed = ow.find(j("Federate")); 
        if fed is None: ET.SubElement(ow, j("Federate")).text = "WARSIM"

        # Common flags
        if unit.find(j("IsInactive")) is None:
            ET.SubElement(unit, j("IsInactive")).text = "false"
        if unit.find(j("IsTransferable")) is None:
            ET.SubElement(unit, j("IsTransferable")).text = "true"
        if unit.find(j("Strength")) is None:
            ET.SubElement(unit, j("Strength")).text = "100"
        if unit.find(j("IsAggCommandable")) is None:
            ET.SubElement(unit, j("IsAggCommandable")).text = "false"

        # MtwsData is not required; remove if present
        mtws = unit.find(j("MtwsData"))
        if mtws is not None:
            unit.remove(mtws)

        # Convert Personnel children -> ECs
        for pn in list(unit.findall(j("Personnel"))):
            ptype = pn.findtext(j("Type")) or "Personnel"
            ec = ET.SubElement(entlist, j("EntityComposition"))
            ec.set('id', new_entity_id())
            ET.SubElement(ec, j("LvcId")).text = new_e()
            ET.SubElement(ec, j("Role")).text = ptype + "_" + (nm.text or lvc.text or "")
            ET.SubElement(ec, j("UnitSuperior")).text = lvc.text
            ET.SubElement(ec, j("ClassName")).text = ptype
            ow2 = ET.SubElement(ec, j("OwningFederate")); ET.SubElement(ow2, j("Federate")).text = "WARSIM"
            unit.remove(pn)

    # ---- Flatten units and set UnitSuperior
    moves = []
    for unit in list(unitlist.findall(".//" + j("Unit"))):
        parent = unit.getparent() if hasattr(unit, "getparent") else None
        if parent is not None and parent is not unitlist:
            sup = unit.find(j("UnitSuperior"))
            if sup is None:
                sup = ET.SubElement(unit, j("UnitSuperior"))
            plvc = parent.findtext(j("LvcId"))
            if plvc:
                sup.text = plvc
            moves.append((parent, unit))

    for parent, unit in moves:
        try:
            parent.remove(unit)
        except Exception:
            pass
        unitlist.append(unit)

    _dedupe_entity_roles(entlist, j)
    for ec in entlist.findall(j('EntityComposition')):
        if not (ec.get('id')):
            ec.set('id', new_entity_id())


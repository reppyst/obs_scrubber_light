#!/usr/bin/env python3

from __future__ import annotations

import sys, traceback, zipfile, random, string, time, copy

from datetime import datetime

from pathlib import Path

import pandas as pd, math

from dataclasses import dataclass

from typing import Any, Dict, List, Optional, Set, Tuple, Iterable, Callable

from collections import defaultdict

from PyQt6.QtCore import Qt, QObject, QThread, pyqtSignal, pyqtSlot

from PyQt6.QtWidgets import (
    QApplication,
    QWidget,
    QTabWidget,
    QVBoxLayout,
    QHBoxLayout,
    QLabel,
    QPushButton,
    QFileDialog,
    QLineEdit,
    QTextEdit,
    QGroupBox,
    QGridLayout,
    QCheckBox,
    QMessageBox,
    QButtonGroup,
    QRadioButton,
    QComboBox,
    QFormLayout,
    QDialog,
    QTreeWidget,
    QTreeWidgetItem,
    QHeaderView,
    QDialogButtonBox,
    QMenu,
    QInputDialog,
    QAbstractItemView,
    QProgressBar,
)

from obs_license import (
    DEFAULT_LICENSE_FILENAME,
    LicenseError,
    LicensePayload,
    cached_license_path,
    describe_license,
    load_first_valid_license,
    load_license_file,
    remember_license_path,
)

try:

    from lxml import etree as ET

    LXML = True

except Exception:

    import xml.etree.ElementTree as ET  # type: ignore

    LXML = False

JTDS_NS = "https://jtds.jten.mil"

NS = {"j": JTDS_NS}

LICENSE_INFO: Optional[LicensePayload] = None



try:

    from dragon_importer_new import (
        import_dragon_enhanced as cli_import_dragon_enhanced,
        normalize_to_jtds_schema as cli_normalize_to_jtds_schema,
        append_unitclasses_to_master as cli_append_unitclasses_to_master,
        DragonImportCancelled,
    )

except Exception:

    cli_import_dragon_enhanced = None
    cli_normalize_to_jtds_schema = None
    cli_append_unitclasses_to_master = None
    class DragonImportCancelled(Exception):
        pass


@dataclass
class ObsModel:

    tree: any
    root: ET._Element
    classdata: ET._Element
    scenario: ET._Element
    unit_list: ET._Element
    entcomp_list: ET._Element


def jfind(elem, path):
    return elem.find(path, NS)


def jfindall(elem, path):
    return elem.findall(path, NS)


def jtag(local: str) -> str:
    return f"{{{JTDS_NS}}}{local}"


def text(elem: Optional[ET._Element]) -> Optional[str]:
    return elem.text if elem is not None else None


def _indent_xml(elem: ET.Element, level: int = 0) -> None:

    indent = "\n" + "  " * level
    if len(elem):
        if not elem.text or not elem.text.strip():
            elem.text = indent + "  "
        for child in list(elem):
            _indent_xml(child, level + 1)
        if not elem.tail or not elem.tail.strip():
            elem.tail = indent
    else:
        if not elem.tail or not elem.tail.strip():
            elem.tail = indent


def _now_iso_seconds_no_tz() -> str:
    """Return 'YYYY-MM-DDTHH:MM:SS' in local time (no timezone suffix)."""
    return datetime.now().strftime("%Y-%m-%dT%H:%M:%S")


def _gen_unit_xml_id(used_ids: Set[str]) -> str:
    """
    Generate a unique Unit @id of the form ID_<epochSeconds>.
    If multiple are created within the same second, increment seconds to preserve uniqueness.
    """
    base = int(time.time())
    seq = 0
    while True:
        cand = f"ID_{base + seq}"
        if cand not in used_ids:
            used_ids.add(cand)
            return cand
        seq += 1


def load_unitlist_map(xml_path: str) -> Dict[str, Dict[str, str]]:
    """
    Build a mapping of MilStd2525CCode -> UnitDisEnumeration attributes
    from a reference unitlist.xml. Works with or without namespaces.
    """
    try:
        root = ET.parse(xml_path).getroot()
    except Exception as e:
        raise ValueError(f"Failed to parse reference XML: {e}")

    def local(t: str) -> str:
        return t.rsplit("}", 1)[-1] if "}" in t else t

    mapping: Dict[str, Dict[str, str]] = {}
    for unit in root.iter():
        if local(unit.tag) != "Unit":
            continue
        code_el = None
        ude_el = None
        for ch in list(unit):
            if local(ch.tag) == "MilStd2525CCode":
                code_el = ch
            elif local(ch.tag) == "UnitDisEnumeration":
                ude_el = ch
        if code_el is not None and code_el.text and ude_el is not None:
            code = code_el.text.strip()
            if code:
                mapping[code] = {k: v for k, v in ude_el.attrib.items()}
    return mapping


def _is_valid_unit_xml_id(val: Optional[str]) -> bool:

    if not val or not val.startswith("ID_"):
        return False
    digits = val[3:]
    return len(digits) == 10 and digits.isdigit()


def _is_valid_timestamp(val: Optional[str]) -> bool:

    if not val:
        return False
    try:
        datetime.strptime(val.strip(), "%Y-%m-%dT%H:%M:%S")
        return True
    except Exception:
        return False


def ensure_unit_metadata(
    model: ObsModel,
    default_side: Optional[str] = None,
    target_units: Optional[Set[ET._Element]] = None,
) -> Tuple[int, int, int]:
    """Ensure each <Unit> has a unique ID/dateTimeStamp and populate SideSuperior
    when UnitSuperior is absent. Returns (ids_assigned, timestamps_assigned, sides_assigned).
    When target_units is provided, only those units are modified (aside from ID uniqueness checks).
    """
    side_hint = (
        default_side.strip().upper()
        if isinstance(default_side, str) and default_side.strip()
        else None
    )
    units = list(_iter_local(model.unit_list, "Unit"))
    target_set: Set[ET._Element] = (
        set(target_units) if target_units is not None else set(units)
    )
    if side_hint is None:
        known_sides: Set[str] = set()
        for unit in target_set:
            side_el = jfind(unit, "j:SideSuperior")
            if side_el is not None and side_el.text and side_el.text.strip():
                known_sides.add(side_el.text.strip().upper())
        if len(known_sides) == 1:
            side_hint = next(iter(known_sides))
    if side_hint is None:
        side_list = jfind(model.scenario, "j:SideList")
        if side_list is not None:
            scenario_sides: Set[str] = set()
            for side in jfindall(side_list, "j:Side"):
                nm = text(jfind(side, "j:Name"))
                if nm and nm.strip():
                    scenario_sides.add(nm.strip().upper())
            if len(scenario_sides) == 1:
                side_hint = next(iter(scenario_sides))
    used_xml_ids: Set[str] = set()
    for ec in _iter_local(model.entcomp_list, "EntityComposition"):
        eid = ec.get("id")
        if eid:
            used_xml_ids.add(eid)
    ids_assigned = 0
    stamps_assigned = 0
    sides_set = 0
    seen_unit_ids: Set[str] = set()
    for unit in units:
        existing_id = unit.get("id")
        if (
            not _is_valid_unit_xml_id(existing_id)
            or existing_id in used_xml_ids
            or existing_id in seen_unit_ids
        ):
            new_id = _gen_unit_xml_id(used_xml_ids)
            unit.set("id", new_id)
            existing_id = new_id
            if unit in target_set:
                ids_assigned += 1
        used_xml_ids.add(existing_id)
        seen_unit_ids.add(existing_id)
        if unit in target_set:
            stamp = unit.get("dateTimeStamp")
            if not _is_valid_timestamp(stamp):
                unit.set("dateTimeStamp", _now_iso_seconds_no_tz())
                stamps_assigned += 1
            sup_el = jfind(unit, "j:UnitSuperior")
            sup_text = sup_el.text.strip() if sup_el is not None and sup_el.text else ""
            if not sup_text and side_hint:
                side_el = jfind(unit, "j:SideSuperior")
                side_text = (
                    side_el.text.strip() if side_el is not None and side_el.text else ""
                )
                if side_el is None:
                    side_el = ET.SubElement(unit, jtag("SideSuperior"))
                if side_text.upper() != side_hint:
                    side_el.text = side_hint
                    sides_set += 1
    return ids_assigned, stamps_assigned, sides_set


def _resolve_unit_side(
    unit: ET._Element, lvc_to_unit: Dict[str, ET._Element]
) -> Optional[str]:

    seen: Set[int] = set()
    current = unit
    while current is not None and id(current) not in seen:
        seen.add(id(current))
        side_el = jfind(current, "j:SideSuperior")
        if side_el is not None and side_el.text and side_el.text.strip():
            return side_el.text.strip().upper()
        sup = text(jfind(current, "j:UnitSuperior"))
        if not sup:
            break
        current = lvc_to_unit.get(sup.strip())
    return None


def fix_empty_flags(model: ObsModel) -> Dict[str, Any]:

    if model is None:
        return {"created": 0, "per_side": {}, "skipped": 0}
    import re

    id_to_unit, _ = collect_unit_maps(model)
    used_xml_ids: Set[str] = set()
    used_lvc_ids: Set[str] = set()
    existing_superiors: Set[str] = set()
    existing_roles: Set[str] = set()
    unit_names: Dict[str, str] = {}
    for unit in _iter_local(model.unit_list, "Unit"):
        uid = unit.get("id")
        if uid:
            used_xml_ids.add(uid.strip())
        lvc = text(jfind(unit, "j:LvcId"))
        if lvc:
            val = lvc.strip()
            if val:
                used_lvc_ids.add(val)
                unit_names[val] = text(jfind(unit, "j:Name")) or val
    for ec in _iter_local(model.entcomp_list, "EntityComposition"):
        eid = ec.get("id")
        if eid:
            used_xml_ids.add(eid.strip())
        elvc = text(jfind(ec, "j:LvcId"))
        if elvc:
            used_lvc_ids.add(elvc.strip())
        sup = text(jfind(ec, "j:UnitSuperior"))
        if sup:
            existing_superiors.add(sup.strip())
        role = text(jfind(ec, "j:Role"))
        if role:
            existing_roles.add(role.strip())
    side_map = {
        "BLUFOR": "HMMWV ARMORED M1114 M2",
        "NEUTRAL": "URAL 375 PKM",
        "OPFOR": "BMP 3M",
    }

    def _role_token(value: Optional[str]) -> str:
        if not value:
            return "UNKNOWN"
        s = str(value).upper()
        s = re.sub(r"[^A-Z0-9]+", "_", s)
        s = re.sub(r"_+", "_", s).strip("_")
        return s or "UNKNOWN"

    created = 0
    skipped = 0
    per_side = {k: 0 for k in side_map}
    lvc_to_unit = id_to_unit
    next_role_num = 1
    for unit in _iter_local(model.unit_list, "Unit"):
        lvc = text(jfind(unit, "j:LvcId"))
        if not lvc:
            continue
        lvc = lvc.strip()
        if not lvc or lvc in existing_superiors:
            continue
        side = _resolve_unit_side(unit, lvc_to_unit)
        if not side:
            skipped += 1
            continue
        class_name = side_map.get(side)
        if not class_name:
            skipped += 1
            continue
        unit_name = unit_names.get(lvc) or lvc
        base_role = _role_token(class_name)
        unit_token = _role_token(unit_name)
        idx = next_role_num
        while True:
            candidate_role = f"{idx}_{base_role}_{unit_token}_CDR"
            if candidate_role not in existing_roles:
                break
            idx += 1
        role_text = candidate_role
        existing_roles.add(role_text)
        next_role_num = idx + 1
        ec = ET.SubElement(model.entcomp_list, jtag("EntityComposition"))
        ec.set("id", _gen_unit_xml_id(used_xml_ids))
        new_lvc = _gen_unique_lvcid("U", used_lvc_ids)
        ET.SubElement(ec, jtag("LvcId")).text = new_lvc
        used_lvc_ids.add(new_lvc)
        ET.SubElement(ec, jtag("Role")).text = role_text
        ET.SubElement(ec, jtag("UnitSuperior")).text = lvc
        ET.SubElement(ec, jtag("ClassName")).text = class_name
        ow = ET.SubElement(ec, jtag("OwningFederate"))
        ET.SubElement(ow, jtag("Federate")).text = "WARSIM"
        ET.SubElement(ec, jtag("IsInactive")).text = "false"
        ET.SubElement(ec, jtag("IsTransferrable")).text = "true"
        ET.SubElement(ec, jtag("IsInvincible")).text = "false"
        per_side[side] += 1
        created += 1
        existing_superiors.add(lvc)
    return {"created": created, "per_side": per_side, "skipped": skipped}


# ---------------- Core loaders/savers ----------------


def load_obs_xml(path: str) -> ObsModel:

    parser = ET.XMLParser(remove_blank_text=True) if LXML else None
    if path.lower().endswith(".zip"):
        with zipfile.ZipFile(path) as z:
            name = next((n for n in z.namelist() if n.lower().endswith(".xml")), None)
            if not name:
                raise ValueError("No .xml found inside zip")
            data = z.read(name)
            if LXML:
                root = (
                    ET.fromstring(data, parser=parser)
                    if parser is not None
                    else ET.fromstring(data)
                )
            else:
                root = ET.fromstring(data)

            class _Shim:
                def __init__(self, r):
                    self._r = r

                def getroot(self):
                    return self._r

            tree = _Shim(root)
    else:
        if LXML:
            tree_parsed = (
                ET.parse(path, parser=parser) if parser is not None else ET.parse(path)
            )
            root = tree_parsed.getroot()

            class _Shim:
                def __init__(self, r):
                    self._r = r

                def getroot(self):
                    return self._r

            tree = _Shim(root)
        else:
            tree = ET.parse(path)
            root = tree.getroot()
    classdata = jfind(root, "j:ClassData")
    scenario = jfind(root, "j:Scenario")
    if classdata is None or scenario is None:
        raise ValueError(
            "Not a recognized JTDS OBS XML (missing <ClassData> or <Scenario>)"
        )
    unit_list = jfind(scenario, "j:UnitList")
    entcomp_list = jfind(scenario, "j:EntityCompositionList")
    if unit_list is None or entcomp_list is None:
        raise ValueError("Missing <UnitList> or <EntityCompositionList>")
    return ObsModel(tree, root, classdata, scenario, unit_list, entcomp_list)


def _new_blank_model() -> ObsModel:

    if LXML:
        root = ET.Element(jtag("JTDS"), nsmap={None: JTDS_NS})
    else:
        root = ET.Element(jtag("JTDS"))
    classdata = ET.SubElement(root, jtag("ClassData"))
    scenario = ET.SubElement(root, jtag("Scenario"))
    unit_list = ET.SubElement(scenario, jtag("UnitList"))
    entcomp_list = ET.SubElement(scenario, jtag("EntityCompositionList"))

    class _Shim:
        def __init__(self, r):
            self._r = r

        def getroot(self):
            return self._r

    tree = _Shim(root)
    return ObsModel(tree, root, classdata, scenario, unit_list, entcomp_list)


def clone_obs_model(model: ObsModel) -> ObsModel:

    if model is None:
        raise ValueError("Cannot clone a null ObsModel")

    if LXML:
        parser = ET.XMLParser(remove_blank_text=True)
        xml_bytes = ET.tostring(model.root)
        root_copy = (
            ET.fromstring(xml_bytes, parser=parser) if parser is not None else ET.fromstring(xml_bytes)
        )

        class _Shim:
            def __init__(self, r):
                self._r = r

            def getroot(self):
                return self._r

        tree_copy = _Shim(root_copy)
    else:
        xml_bytes = ET.tostring(model.root)
        root_copy = ET.fromstring(xml_bytes)

        class _Shim:
            def __init__(self, r):
                self._r = r

            def getroot(self):
                return self._r

        tree_copy = _Shim(root_copy)

    classdata = jfind(root_copy, "j:ClassData")
    scenario = jfind(root_copy, "j:Scenario")
    if classdata is None or scenario is None:
        raise ValueError("Cloned OBS XML is missing required JTDS sections")
    unit_list = jfind(scenario, "j:UnitList")
    entcomp_list = jfind(scenario, "j:EntityCompositionList")
    if unit_list is None or entcomp_list is None:
        raise ValueError("Cloned OBS XML lacks UnitList/EntityCompositionList")

    cloned = ObsModel(tree_copy, root_copy, classdata, scenario, unit_list, entcomp_list)
    base_fields = {"tree", "root", "classdata", "scenario", "unit_list", "entcomp_list"}
    for key, value in vars(model).items():
        if key in base_fields:
            continue
        try:
            setattr(cloned, key, copy.deepcopy(value))
        except Exception:
            setattr(cloned, key, value)
    return cloned


def save_xml(model: ObsModel, out_path: str):

    ensure_unit_metadata(model)
    if LXML:
        xml_bytes = ET.tostring(
            model.root, pretty_print=True, xml_declaration=True, encoding="UTF-8"
        )
        with open(out_path, "wb") as f:
            f.write(xml_bytes)
    else:
        _indent_xml(model.root)
        ET.ElementTree(model.root).write(
            out_path, encoding="utf-8", xml_declaration=True
        )


# ---------------- Utilities ----------------


def collect_unit_maps(
    model: ObsModel,
) -> Tuple[Dict[str, ET._Element], Dict[str, List[ET._Element]]]:

    id_to_unit, parent_to_children = {}, {}
    for u in list(model.unit_list):
        lid = text(jfind(u, "j:LvcId"))
        if lid:
            id_to_unit[lid] = u
    for u in list(model.unit_list):
        lid = text(jfind(u, "j:LvcId"))
        parent = text(jfind(u, "j:UnitSuperior"))
        if parent:
            parent_to_children.setdefault(parent, []).append(u)
        if lid and lid not in parent_to_children:
            parent_to_children.setdefault(lid, [])
    return id_to_unit, parent_to_children


def clone_element(elem: ET._Element) -> ET._Element:
    """Return a deep copy of *elem* that is safe across XML backends."""
    return copy.deepcopy(elem)


DEFAULT_SIDE_ORDER = ["BLUFOR", "OPFOR", "NEUTRAL", "CIVILIAN", "UNKNOWN"]


def format_unit_label(unit: ET._Element) -> str:

    name = (text(jfind(unit, "j:Name")) or "").strip() or "Unnamed Unit"
    echelon = (text(jfind(unit, "j:Echelon")) or "").strip()
    lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
    parts = [name]
    if echelon:
        parts.append(f"({echelon})")
    if lvc:
        parts.append(f"[{lvc}]")
    return " ".join(parts)


def format_entity_label(
    ec: ET._Element,
    *,
    include_superior: bool = False,
    superior_hint: Optional[str] = None,
) -> str:

    role = (text(jfind(ec, "j:Role")) or "").strip() or "Role"
    qty = (text(jfind(ec, "j:Quantity")) or "").strip()
    lvc = (text(jfind(ec, "j:LvcId")) or "").strip()
    parts = [role]
    if qty:
        parts.append(f"x{qty}")
    if lvc:
        parts.append(f"[{lvc}]")
    if include_superior:
        sup = superior_hint or (text(jfind(ec, "j:UnitSuperior")) or "").strip()
        if sup:
            parts.append(f"(Unit {sup})")
    return " ".join(parts)


def unit_sort_key(unit: ET._Element) -> Tuple[int, str, str]:

    echelon = (text(jfind(unit, "j:Echelon")) or "").strip()
    rank = ECHELON_RANK.get(echelon, len(ECHELON_ORDER))
    name = (text(jfind(unit, "j:Name")) or "").strip()
    lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
    return (rank, name.lower(), lvc)


def entity_sort_key(ec: ET._Element) -> Tuple[str, str]:

    role = (text(jfind(ec, "j:Role")) or "").strip()
    lvc = (text(jfind(ec, "j:LvcId")) or "").strip()
    return (role.lower(), lvc)


def side_sort_key(side: str) -> Tuple[int, str]:

    try:
        idx = DEFAULT_SIDE_ORDER.index(side)
    except ValueError:
        idx = len(DEFAULT_SIDE_ORDER)
    return (idx, side)


def ensure_side_entries(model: ObsModel, sides: Iterable[str]) -> int:
    """Ensure that *sides* exist inside <SideList>; return how many were added."""
    normalized = [s.strip() for s in sides if s and s.strip()]
    if not normalized:
        return 0
    side_list = jfind(model.scenario, "j:SideList")
    if side_list is None:
        side_list = ET.SubElement(model.scenario, jtag("SideList"))
    existing: Set[str] = set()
    for side_elem in list(side_list):
        name = text(jfind(side_elem, "j:Name"))
        if name:
            existing.add(name.strip().upper())
    added = 0
    for side in normalized:
        key = side.upper()
        if key in existing:
            continue
        side_elem = ET.SubElement(side_list, jtag("Side"))
        ET.SubElement(side_elem, jtag("Name")).text = side
        existing.add(key)
        added += 1
    return added


NAME_ECHELON_TOKENS: Set[str] = {
    "TEAM",
    "DETACHMENT",
    "DET",
    "SECTION",
    "SECT",
    "SEC",
    "SQUAD",
    "SQD",
    "PLATOON",
    "PLT",
    "COMPANY",
    "COMP",
    "CO",
    "BATTERY",
    "BTRY",
    "BATTALION",
    "BN",
    "REGIMENT",
    "REGT",
    "BRIGADE",
    "BDE",
    "DIVISION",
    "DIV",
    "CORPS",
    "ARMY",
    "WING",
    "GROUP",
    "SQDN",
    "SQUADRON",
    "FLT",
    "FLIGHT",
    "HQ",
    "HQTRS",
    "COMMAND",
    "CMD",
    "TASKFORCE",
    "TF",
}


def _split_unit_name_components(name: str) -> Tuple[str, str]:

    tokens = [tok for tok in name.split("_") if tok]
    if not tokens:
        return name, ""
    for idx, tok in enumerate(tokens):
        up = tok.upper()
        if up in NAME_ECHELON_TOKENS or tok.isdigit():
            base = "_".join(tokens[:idx])
            suffix = "_".join(tokens[idx:])
            return base or name, suffix
    return name, ""


def _gather_unit_descendants(
    root: ET._Element,
    parent_to_children: Dict[str, List[ET._Element]],
    include_root: bool = False,
) -> List[ET._Element]:

    collected: List[ET._Element] = []
    visited: Set[int] = set()

    def visit(unit: ET._Element) -> None:
        key = id(unit)
        if key in visited:
            return
        visited.add(key)
        if unit is not root or include_root:
            collected.append(unit)
        lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        children = parent_to_children.get(lvc, []) if lvc else []
        for child in children:
            visit(child)

    visit(root)
    return collected


def _local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1] if "}" in tag else tag


def _iter_local(root: ET._Element, local: str):

    for e in root.iter():
        if _local(e.tag) == local:
            yield e


_DISCODE_ATTRS = (
    "kind",
    "domain",
    "country",
    "category",
    "subcategory",
    "specific",
    "extra",
)

# Branch detection (token-based)

BRANCH_TOKENS = {
    "SIG": ["SIG", "SIGNAL"],
    "MNT": ["MNT", "MAINT"],
    "ENG": ["ENG", "ENGINEER", "ENGR"],
    "MED": ["MED", "MEDICAL"],
    "SPT": ["SPT", "SUPPORT", "CSS"],
    "CHEM": ["CHEM", "CBRN", "NBC"],
}


def unit_branch(u: ET._Element) -> Optional[str]:

    name = (text(jfind(u, "j:Name")) or "").upper()
    cls = (text(jfind(u, "j:ClassName")) or "").upper()
    code = (text(jfind(u, "j:MilStd2525CCode")) or "").upper()
    hay = " ".join([name, cls, code])
    for k, toks in BRANCH_TOKENS.items():
        if any(t in hay for t in toks):
            return k
    return None


HQ_KEYWORDS = ("HQ", "HEADQUARTERS")


def is_hq_unit(unit: ET._Element) -> bool:

    name = (text(jfind(unit, "j:Name")) or "").strip().upper()
    return any(keyword in name for keyword in HQ_KEYWORDS)


ECHELON_CANONICAL = {
    "TEAM": "Team",
    "FIRETEAM": "Team",
    "SECTION": "Section",
    "SECT": "Section",
    "SEC": "Section",
    "DETACHMENT": "Section",
    "DET": "Section",
    "SQUAD": "Squad",
    "SQD": "Squad",
    "PLATOON": "Platoon",
    "PLT": "Platoon",
    "COMPANY": "Company/Battery",
    "CO": "Company/Battery",
    "COMPANY/BATTERY": "Company/Battery",
    "BATTERY": "Company/Battery",
    "BTRY": "Company/Battery",
    "BATTALION": "Battalion",
    "BN": "Battalion",
    "REGIMENT": "Brigade",
    "REGT": "Brigade",
    "BRIGADE": "Brigade",
    "BDE": "Brigade",
    "DIVISION": "Division",
    "DIV": "Division",
    "CORPS": "Corps",
    "ARMY": "Army",
}

ECHELON_ORDER = [
    "Team",
    "Section",
    "Squad",
    "Platoon",
    "Company/Battery",
    "Battalion",
    "Brigade",
    "Division",
    "Corps",
    "Army",
]

ECHELON_RANK = {e: i for i, e in enumerate(ECHELON_ORDER)}

CONSOLIDATION_LEVELS = [
    "Section",
    "Platoon",
    "Company/Battery",
    "Battalion",
    "Brigade",
    "Division",
]


def normalize_echelon(value: Optional[str]) -> str:

    if not value:
        return ""
    key = str(value).strip().upper()
    return ECHELON_CANONICAL.get(key, str(value).strip())


def unit_echelon(u: ET._Element) -> str:

    direct = normalize_echelon(text(jfind(u, "j:Echelon")))
    if direct:
        return direct
    name_hint = (text(jfind(u, "j:Name")) or "").upper()
    for guess, token in [
        ("Platoon", " PLT"),
        ("Company/Battery", " CO "),
        ("Company/Battery", " CO_"),
        ("Company/Battery", " CO-"),
        ("Battalion", " BN"),
        ("Brigade", " BDE"),
        ("Division", " DIV"),
        ("Section", " SEC"),
        ("Squad", " SQD"),
        ("Team", " TEAM"),
    ]:
        if token in name_hint:
            return normalize_echelon(guess)
    return ""


def _entity_class_name(node: ET._Element) -> Optional[str]:

    for child in list(node):
        if _local(child.tag) == "ClassName" and child.text:
            return child.text.strip()
    if _local(node.tag) == "ClassName" and node.text:
        return node.text.strip()
    direct = jfind(node, "j:ClassName")
    if direct is not None and direct.text:
        return direct.text.strip()
    return None


def _collect_ecc_class_names(ecc: ET._Element) -> Set[str]:

    labels: Set[str] = set()
    for child in list(ecc):
        if _local(child.tag) in ("Name", "ClassName") and child.text:
            labels.add(child.text.strip())
    for tag in ("Name", "ClassName"):
        node = jfind(ecc, f"j:{tag}")
        if node is not None and node.text:
            labels.add(node.text.strip())
    return {label for label in labels if label}


def _normalize_discode_component(value: str) -> str:

    trimmed = value.strip()
    if trimmed.isdigit():
        return str(int(trimmed))
    return trimmed


def _parse_discode_query(raw: str) -> Dict[str, str]:

    text_val = (raw or "").strip()
    if not text_val:
        raise ValueError("Enter a DisCode value.")
    parts = [part.strip() for part in text_val.split(".") if part.strip()]
    if len(parts) != len(_DISCODE_ATTRS):
        raise ValueError(
            "DisCode must contain 7 dot-separated integers (kind.domain.country.category.subcategory.specific.extra)."
        )
    attrs: Dict[str, str] = {}
    for key, part in zip(_DISCODE_ATTRS, parts):
        if not part.isdigit():
            raise ValueError(f"DisCode component '{part}' for '{key}' must be numeric.")
        attrs[key] = str(int(part))
    return attrs


def _discode_matches(node: ET._Element, expected: Dict[str, str]) -> bool:

    for key, value in expected.items():
        actual = node.get(key)
        if actual is None:
            return False
        if _normalize_discode_component(actual) != value:
            return False
    return True


# Personnel crosswalk via ClassData (kind=3)


def _class_names_for_disc_kind(model: ObsModel, kind: str) -> Set[str]:

    names: Set[str] = set()
    for ecc in _iter_local(model.classdata, "EntityCompositionClass"):
        discode = next((ch for ch in list(ecc) if _local(ch.tag) == "DisCode"), None)
        if discode is None:
            discode = next((ch for ch in _iter_local(ecc, "DisCode")), None)
        if discode is not None and discode.get("kind") == kind:
            cname = None
            for cand in ["Name", "ClassName", "TypeName"]:
                el = next(
                    (x for x in list(ecc) if _local(x.tag) == cand and x.text), None
                )
                if el is not None:
                    cname = el.text.strip()
                    break
            if cname:
                names.add(cname)
    return names


def _personnel_class_names(model: ObsModel) -> Set[str]:

    return _class_names_for_disc_kind(model, "3")


def _munitions_class_names(model: ObsModel) -> Set[str]:

    return _class_names_for_disc_kind(model, "2")


def count_personnel(model: ObsModel) -> int:

    pnames = _personnel_class_names(model)
    if not pnames:
        return 0
    cnt = 0
    for child in list(model.entcomp_list):
        cname = None
        for e in list(child):
            if _local(e.tag) == "ClassName" and e.text:
                cname = e.text.strip()
                break
        if cname is None and _local(child.tag) == "ClassName" and child.text:
            cname = child.text.strip()
        if cname and cname in pnames:
            cnt += 1
    return cnt


def _remove_entities_for_kind(
    model: ObsModel, kind: str, *, removed_lvc_ids: Optional[Set[str]] = None
) -> Tuple[int, int]:

    names = _class_names_for_disc_kind(model, kind)
    if not names:
        return 0, 0
    removed_ec = 0
    for child in list(model.entcomp_list):
        if _local(child.tag) != "EntityComposition":
            continue
        matched = False
        cname = _entity_class_name(child)
        if cname and cname in names:
            matched = True
        else:
            discode = next(
                (ch for ch in list(child) if _local(ch.tag) == "DisCode"), None
            )
            if discode is None:
                discode = next((ch for ch in _iter_local(child, "DisCode")), None)
            if discode is not None and discode.get("kind") == kind:
                matched = True
        if not matched:
            continue
        if removed_lvc_ids is not None:
            lvc = (text(jfind(child, "j:LvcId")) or "").strip()
            if lvc:
                removed_lvc_ids.add(lvc.upper())
        model.entcomp_list.remove(child)
        removed_ec += 1
    removed_ecc = 0
    ecc_list = jfind(model.classdata, jtag("EntityCompositionClassList"))
    if ecc_list is not None:
        for ecc in list(ecc_list):
            discode = next(
                (ch for ch in list(ecc) if _local(ch.tag) == "DisCode"), None
            )
            if discode is None:
                discode = next((ch for ch in _iter_local(ecc, "DisCode")), None)
            if discode is not None and discode.get("kind") == kind:
                ecc_list.remove(ecc)
                removed_ecc += 1
    return removed_ec, removed_ecc


def _prune_entity_crew_lists(model: ObsModel, removed_lvc_ids: Set[str]) -> int:

    if not removed_lvc_ids:
        return 0
    normalized = {lid.strip().upper() for lid in removed_lvc_ids if lid and lid.strip()}
    if not normalized:
        return 0
    item_tags = {"Crew", "Passenger"}
    container_tags = {"CrewList", "PassengerList"}

    def _find_parent(root: ET._Element, target: ET._Element) -> Optional[ET._Element]:
        if hasattr(target, "getparent"):
            parent = target.getparent()  # type: ignore[attr-defined]
            if parent is not None:
                return parent
        for candidate in root.iter():
            for child in list(candidate):
                if child is target:
                    return candidate
        return None

    removed = 0
    for entity in list(model.entcomp_list):
        containers = [
            node for node in list(entity.iter()) if _local(node.tag) in container_tags
        ]
        for container in containers:
            items = [
                child for child in list(container) if _local(child.tag) in item_tags
            ]
            for item in items:
                raw_lvc = (
                    item.get("lvcId") or item.get("lvcID") or item.get("lvcid") or ""
                )
                crew_lvc = raw_lvc.strip()
                if crew_lvc and crew_lvc.upper() in normalized:
                    container.remove(item)
                    removed += 1
            remaining_items = [
                child for child in list(container) if _local(child.tag) in item_tags
            ]
            if not remaining_items:
                parent = _find_parent(entity, container)
                if parent is not None:
                    parent.remove(container)
                    if _local(parent.tag) == "Platform" and len(list(parent)) == 0:
                        grandparent = _find_parent(entity, parent)
                        if grandparent is not None:
                            grandparent.remove(parent)
                else:
                    if container in list(entity):
                        entity.remove(container)
    return removed


def remove_entities_by_discode(model: ObsModel, discode_value: str) -> Tuple[int, int]:

    attrs = _parse_discode_query(discode_value)
    matching_labels: Set[str] = set()
    removed_ecc = 0
    ecc_list = jfind(model.classdata, jtag("EntityCompositionClassList"))
    if ecc_list is not None:
        for ecc in list(ecc_list):
            discode = next(
                (ch for ch in list(ecc) if _local(ch.tag) == "DisCode"), None
            )
            if discode is None:
                discode = next((ch for ch in _iter_local(ecc, "DisCode")), None)
            if discode is not None and _discode_matches(discode, attrs):
                matching_labels.update(_collect_ecc_class_names(ecc))
                ecc_list.remove(ecc)
                removed_ecc += 1
    removed_ec = 0
    for entity in list(model.entcomp_list):
        matched = False
        cname = _entity_class_name(entity)
        if cname and cname in matching_labels:
            matched = True
        else:
            discode = next(
                (ch for ch in list(entity) if _local(ch.tag) == "DisCode"), None
            )
            if discode is None:
                discode = next((ch for ch in _iter_local(entity, "DisCode")), None)
            if discode is not None and _discode_matches(discode, attrs):
                matched = True
        if matched:
            model.entcomp_list.remove(entity)
            removed_ec += 1
    return removed_ec, removed_ecc


def replace_discode_entries(
    model: ObsModel, old_value: str, new_value: str
) -> Tuple[int, int]:

    old_attrs = _parse_discode_query(old_value)
    new_attrs = _parse_discode_query(new_value)
    updated_ecc = 0
    ecc_list = jfind(model.classdata, jtag("EntityCompositionClassList"))
    if ecc_list is not None:
        for ecc in list(ecc_list):
            discode = next(
                (ch for ch in list(ecc) if _local(ch.tag) == "DisCode"), None
            )
            if discode is None:
                discode = next((ch for ch in _iter_local(ecc, "DisCode")), None)
            if discode is not None and _discode_matches(discode, old_attrs):
                for key, value in new_attrs.items():
                    discode.set(key, value)
                updated_ecc += 1
    updated_entities = 0
    for entity in list(model.entcomp_list):
        discode = next((ch for ch in list(entity) if _local(ch.tag) == "DisCode"), None)
        if discode is None:
            discode = next((ch for ch in _iter_local(entity, "DisCode")), None)
        if discode is not None and _discode_matches(discode, old_attrs):
            for key, value in new_attrs.items():
                discode.set(key, value)
            updated_entities += 1
    return updated_ecc, updated_entities


def remove_unused_entity_composition_classes(
    model: ObsModel,
) -> Tuple[int, List[str], int]:

    used_names: Set[str] = set()
    for entity in list(model.entcomp_list):
        if _local(entity.tag) != "EntityComposition":
            continue
        cname = _entity_class_name(entity)
        if cname:
            used_names.add(cname)
    ecc_list = jfind(model.classdata, jtag("EntityCompositionClassList"))
    if ecc_list is None:
        return 0, [], 0
    removed = 0
    removed_labels: Set[str] = set()
    unnamed = 0
    for ecc in list(ecc_list):
        if _local(ecc.tag) != "EntityCompositionClass":
            continue
        labels = _collect_ecc_class_names(ecc)
        if labels & used_names:
            continue
        ecc_list.remove(ecc)
        removed += 1
        if labels:
            removed_labels.update(labels)
        else:
            unnamed += 1
    return removed, sorted(removed_labels), unnamed


def find_missing_entity_composition_classes(model: ObsModel) -> List[str]:

    used_names: Set[str] = set()
    for entity in list(model.entcomp_list):
        if _local(entity.tag) != "EntityComposition":
            continue
        cname = _entity_class_name(entity)
        if cname:
            used_names.add(cname)
    defined_names: Set[str] = set()
    ecc_list = jfind(model.classdata, jtag("EntityCompositionClassList"))
    if ecc_list is not None:
        for ecc in list(ecc_list):
            if _local(ecc.tag) != "EntityCompositionClass":
                continue
            defined_names.update(_collect_ecc_class_names(ecc))
    return sorted(name for name in used_names if name not in defined_names)


def remove_personnel(model: ObsModel) -> Tuple[int, int]:

    removed_lvc: Set[str] = set()
    removed_ec, removed_ecc = _remove_entities_for_kind(
        model, "3", removed_lvc_ids=removed_lvc
    )
    _prune_entity_crew_lists(model, removed_lvc)
    return removed_ec, removed_ecc


def remove_munitions(model: ObsModel) -> Tuple[int, int]:

    return _remove_entities_for_kind(model, "2")


def purge_classdata_sections(
    model: ObsModel, supply=False, emitter=False, munitions=False, flyout=False
) -> Dict[str, int]:

    counts = {}
    for want, tag in [
        (supply, "SupplyClassList"),
        (emitter, "EmitterClassList"),
        (munitions, "MunitionsList"),
        (flyout, "FlyOutList"),
    ]:
        if want:
            node = jfind(model.classdata, f"j:{tag}")
            counts[tag] = len(list(node)) if node is not None else 0
            if node is not None:
                model.classdata.remove(node)
    return counts


def remove_unit_subtree(model: ObsModel, root_lvc: str) -> Tuple[int, int]:

    if not root_lvc:
        return (0, 0)
    id_to_unit, parent_to_children = collect_unit_maps(model)
    to_remove: Set[str] = set()

    def mark(lvc: str) -> None:
        if not lvc or lvc in to_remove:
            return
        to_remove.add(lvc)
        for child in parent_to_children.get(lvc, []):
            child_lvc = (text(jfind(child, "j:LvcId")) or "").strip()
            if child_lvc:
                mark(child_lvc)

    mark(root_lvc)
    if not to_remove:
        return (0, 0)
    removed_ec = 0
    for ec in list(model.entcomp_list):
        sup = (text(jfind(ec, "j:UnitSuperior")) or "").strip()
        if sup and sup in to_remove:
            model.entcomp_list.remove(ec)
            removed_ec += 1
    removed_units = 0
    for unit in list(model.unit_list):
        lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        if lvc and lvc in to_remove:
            model.unit_list.remove(unit)
            removed_units += 1
    return removed_units, removed_ec


def remove_units_by_branch(model: ObsModel, branches: Set[str]) -> Tuple[int, int]:

    id_to_unit, parent_to_children = collect_unit_maps(model)
    to_remove_units: Set[str] = set()

    def mark_subtree(lvcid: str):
        if lvcid in to_remove_units:
            return
        to_remove_units.add(lvcid)
        for child in parent_to_children.get(lvcid, []):
            clid = text(jfind(child, "j:LvcId"))
            if clid:
                mark_subtree(clid)

    for lid, u in id_to_unit.items():
        br = unit_branch(u)
        if br and br in branches:
            mark_subtree(lid)
    removed_ec = 0
    for ec in list(model.entcomp_list):
        sup = text(jfind(ec, "j:UnitSuperior"))
        if sup and sup in to_remove_units:
            model.entcomp_list.remove(ec)
            removed_ec += 1
    removed_units = 0
    for u in list(model.unit_list):
        lid = text(jfind(u, "j:LvcId"))
        if lid and lid in to_remove_units:
            model.unit_list.remove(u)
            removed_units += 1
    return removed_units, removed_ec


def remove_side(model: ObsModel, side_name: str) -> Tuple[int, int]:

    id_to_unit, parent_to_children = collect_unit_maps(model)
    roots: Set[str] = set()
    for lid, u in id_to_unit.items():
        ss = text(jfind(u, "j:SideSuperior"))
        if ss and ss.strip().upper() == side_name.upper():
            roots.add(lid)
    to_remove: Set[str] = set()

    def mark(lid: str):
        if not lid or lid in to_remove:
            return
        to_remove.add(lid)
        for ch in parent_to_children.get(lid, []):
            clid = text(jfind(ch, "j:LvcId"))
            if clid:
                mark(clid)

    for r in roots:
        mark(r)
    removed_ec = 0
    for ec in list(model.entcomp_list):
        sup = text(jfind(ec, "j:UnitSuperior"))
        if sup and sup in to_remove:
            model.entcomp_list.remove(ec)
            removed_ec += 1
    removed_units = 0
    for u in list(model.unit_list):
        lid = text(jfind(u, "j:LvcId"))
        if lid and lid in to_remove:
            model.unit_list.remove(u)
            removed_units += 1
    return removed_units, removed_ec


# Consolidation + LvcId helpers


def consolidate_units(
    model: ObsModel,
    target_label: str,
    sides: Optional[Set[str]] = None,
    scope_roots: Optional[Set[str]] = None,
) -> Dict[str, int]:

    option = (target_label or "").strip()
    stats: Dict[str, int] = {
        "removed_units": 0,
        "moved_entity_compositions": 0,
        "relinked_units": 0,
        "skipped_units": 0,
    }
    if not option or option == "None":
        return stats
    target_echelon = normalize_echelon(option) or option
    target_rank = ECHELON_RANK.get(target_echelon, len(ECHELON_ORDER))
    protected_rank = ECHELON_RANK.get(
        "Company/Battery", ECHELON_RANK.get("Company", target_rank)
    )
    side_filter = {s.upper() for s in sides} if sides else None
    id_to_unit, parent_to_children = collect_unit_maps(model)
    if not id_to_unit:
        return stats
    root_ids: Set[str] = set()
    if scope_roots:
        for root in scope_roots:
            if root:
                root_ids.add(root.strip())
    scope_ids: Optional[Set[str]] = None
    if root_ids:
        scope_ids = set()
        to_visit = list(root_ids)
        while to_visit:
            current = (to_visit.pop() or "").strip()
            if not current or current in scope_ids:
                continue
            unit_elem = id_to_unit.get(current)
            if unit_elem is None:
                continue
            scope_ids.add(current)
            for child in parent_to_children.get(current, []):
                child_id = (text(jfind(child, "j:LvcId")) or "").strip()
                if child_id and child_id not in scope_ids:
                    to_visit.append(child_id)
        if not scope_ids:
            return stats
        root_ids = {rid for rid in root_ids if rid in scope_ids}
    parent_map: Dict[str, Optional[str]] = {}
    for lvc, unit in id_to_unit.items():
        sup = text(jfind(unit, "j:UnitSuperior"))
        parent_map[lvc] = sup.strip() if sup and sup.strip() else None
    side_cache: Dict[str, str] = {}

    def unit_side_value(lvc: Optional[str]) -> str:
        if not lvc:
            return "UNKNOWN"
        if lvc in side_cache:
            return side_cache[lvc]
        unit = id_to_unit.get(lvc)
        if unit is None:
            side_cache[lvc] = "UNKNOWN"
            return "UNKNOWN"
        side = (text(jfind(unit, "j:SideSuperior")) or "").strip()
        if side:
            side_cache[lvc] = side.upper()
            return side_cache[lvc]
        parent = parent_map.get(lvc)
        resolved = unit_side_value(parent)
        side_cache[lvc] = resolved
        return resolved

    kept_units: Set[str] = set()
    explicit_kept: Set[str] = set()
    to_remove: Set[str] = set()
    for lvc, unit in id_to_unit.items():
        if scope_ids is not None and lvc not in scope_ids:
            continue
        rank = ECHELON_RANK.get(unit_echelon(unit), len(ECHELON_ORDER))
        if rank > target_rank:
            continue
        if root_ids and lvc in root_ids:
            explicit_kept.add(lvc)
            continue
        unit_side = unit_side_value(lvc)
        if side_filter and unit_side not in side_filter:
            continue
        if rank >= protected_rank and is_hq_unit(unit):
            kept_units.add(lvc)
            continue
        to_remove.add(lvc)
    if not to_remove:
        stats["skipped_units"] = len(kept_units) + len(explicit_kept)
        return stats
    hq_by_parent: Dict[Optional[str], List[str]] = defaultdict(list)
    for hq in kept_units:
        parent = parent_map.get(hq)
        hq_by_parent[parent].append(hq)
    for parent, items in hq_by_parent.items():
        items.sort(key=lambda l: (text(jfind(id_to_unit[l], "j:Name")) or "").lower())
    ec_by_superior: Dict[str, List[ET._Element]] = defaultdict(list)
    for ec in list(model.entcomp_list):
        sup = text(jfind(ec, "j:UnitSuperior"))
        if sup and sup.strip():
            ec_by_superior[sup.strip()].append(ec)
    ROOT_PARENT = "__ROOT__"
    used_names: Dict[str, Set[str]] = defaultdict(set)

    def parent_key(pid: Optional[str]) -> str:
        return pid if pid else ROOT_PARENT

    for lvc, unit in id_to_unit.items():
        if lvc in to_remove:
            continue
        parent = parent_map.get(lvc)
        if parent in to_remove:
            continue
        name_val = (text(jfind(unit, "j:Name")) or "").strip()
        if name_val:
            used_names[parent_key(parent)].add(name_val.casefold())
    depth_cache: Dict[str, int] = {}

    def depth_of(lvc: str) -> int:
        if lvc in depth_cache:
            return depth_cache[lvc]
        depth = 0
        cur = parent_map.get(lvc)
        seen: Set[str] = {lvc}
        while cur:
            depth += 1
            if cur in depth_cache:
                depth += depth_cache[cur]
                break
            if cur in seen:
                break
            seen.add(cur)
            cur = parent_map.get(cur)
        depth_cache[lvc] = depth
        return depth

    def preferred_rollup_parent(lvc: str) -> Optional[str]:
        cur = parent_map.get(lvc)
        seen: Set[str] = set()
        while cur:
            if cur in seen:
                break
            if cur not in to_remove:
                hqs = hq_by_parent.get(cur)
                if hqs:
                    return hqs[0]
                return cur
            seen.add(cur)
            cur = parent_map.get(cur)
        return None

    target_parent_for: Dict[str, Optional[str]] = {}
    skipped: Set[str] = set()
    for lvc in list(to_remove):
        target_parent = preferred_rollup_parent(lvc)
        if target_parent is None:
            skipped.add(lvc)
        else:
            target_parent_for[lvc] = target_parent
    if skipped:
        to_remove.difference_update(skipped)
    stats["skipped_units"] = len(kept_units) + len(skipped) + len(explicit_kept)
    if not to_remove:
        return stats

    def ensure_unique_name(
        node: ET._Element, parent_id: Optional[str], source_label: str
    ) -> None:
        key = parent_key(parent_id)
        used = used_names.setdefault(key, set())
        name_elem = jfind(node, "j:Name")
        base = (text(name_elem) or "").strip()
        if not base:
            base = (source_label or "").strip() or "Unit"
        candidate = base
        prefix = (source_label or "").strip()
        if candidate.casefold() in used:
            candidate = f"{prefix} - {base}" if prefix else base
            idx = 2
            while candidate.casefold() in used:
                suffix = f" ({idx})"
                candidate = (
                    f"{prefix} - {base}{suffix}" if prefix else f"{base}{suffix}"
                )
                idx += 1
        if name_elem is None:
            name_elem = ET.Element(jtag("Name"))
            node.insert(0, name_elem)
        name_elem.text = candidate
        used.add(candidate.casefold())

    sorted_targets = sorted(to_remove, key=depth_of, reverse=True)
    for lvc in sorted_targets:
        unit_elem = id_to_unit.get(lvc)
        if unit_elem is None:
            continue
        target_parent = target_parent_for.get(lvc)
        children = list(parent_to_children.get(lvc, []))
        source_label = (text(jfind(unit_elem, "j:Name")) or "").strip()
        for child in children:
            child_id = text(jfind(child, "j:LvcId"))
            if not child_id:
                continue
            existing = parent_to_children.get(lvc)
            if existing and child in existing:
                existing.remove(child)
            if target_parent:
                parent_to_children.setdefault(target_parent, []).append(child)
            sup_elem = jfind(child, "j:UnitSuperior")
            if target_parent:
                if sup_elem is None:
                    sup_elem = ET.Element(jtag("UnitSuperior"))
                    child.insert(0, sup_elem)
                sup_elem.text = target_parent
            elif sup_elem is not None:
                child.remove(sup_elem)
            parent_map[child_id] = target_parent
            if child_id not in to_remove:
                ensure_unique_name(child, target_parent, source_label)
                stats["relinked_units"] += 1
        for ec in ec_by_superior.get(lvc, []):
            sup_elem = jfind(ec, "j:UnitSuperior")
            if sup_elem is None:
                sup_elem = ET.Element(jtag("UnitSuperior"))
                ec.insert(0, sup_elem)
            sup_elem.text = target_parent or ""
            stats["moved_entity_compositions"] += 1
            if target_parent:
                ec_by_superior[target_parent].append(ec)
        parent_to_children.pop(lvc, None)
        try:
            model.unit_list.remove(unit_elem)
        except ValueError:
            pass
        id_to_unit.pop(lvc, None)
        parent_map.pop(lvc, None)
        stats["removed_units"] += 1
    return stats


def autofill_unique_lvcids(model: ObsModel) -> int:

    used: Set[str] = set()

    def record(elem):
        lid_elem = jfind(elem, "j:LvcId")
        if lid_elem is not None and lid_elem.text:
            used.add(lid_elem.text)

    for u in list(model.unit_list):
        record(u)
    for ec in list(model.entcomp_list):
        record(ec)
    counts: Dict[str, int] = {}
    for u in list(model.unit_list):
        lid = text(jfind(u, "j:LvcId"))
        if lid:
            counts[lid] = counts.get(lid, 0) + 1
    for ec in list(model.entcomp_list):
        lid = text(jfind(ec, "j:LvcId"))
        if lid:
            counts[lid] = counts.get(lid, 0) + 1
    used = set([k for k, v in counts.items() if v == 1])

    def new_id(prefix="U", length=10):
        while True:
            cand = prefix + "".join(
                random.choices(string.ascii_uppercase + string.digits, k=length)
            )
            if cand not in used:
                used.add(cand)
                return cand

    changed = 0
    for u in list(model.unit_list):
        lid_elem = jfind(u, "j:LvcId")
        if lid_elem is None or not lid_elem.text or counts.get(lid_elem.text, 0) > 1:
            new = new_id("U")
            if lid_elem is None:
                lid_elem = ET.Element(jtag("LvcId"))
                u.insert(0, lid_elem)
            lid_elem.text = new
            changed += 1
    for ec in list(model.entcomp_list):
        lid_elem = jfind(ec, "j:LvcId")
        if lid_elem is None or not lid_elem.text or counts.get(lid_elem.text, 0) > 1:
            new = new_id("E")
            if lid_elem is None:
                lid_elem = ET.Element(jtag("LvcId"))
                ec.insert(0, lid_elem)
            lid_elem.text = new
            changed += 1
    return changed


# ---------------- DRAGON Import helpers ----------------


def _expand_echelon(e: Optional[str]) -> Optional[str]:

    if not e:
        return e
    m = {
        "BN": "Battalion",
        "BATTALION": "Battalion",
        "CO": "Company",
        "COMPANY": "Company",
        "BDE": "Brigade",
        "BRIGADE": "Brigade",
        "PLT": "Platoon",
        "PLATOON": "Platoon",
        "DIV": "Division",
        "DIVISION": "Division",
        "CORPS": "Corps",
        "ARMY": "Army",
    }
    key = str(e).strip().upper()
    return m.get(key, e)


def _sanitize_unit_name(name: Optional[str]) -> Optional[str]:

    if not name:
        return name
    return str(name).replace(" ", "_")


def _gen_unique_lvcid(prefix: str, used: Set[str], length: int = 10) -> str:

    while True:
        cand = prefix + "".join(
            random.choices(string.ascii_uppercase + string.digits, k=length)
        )
        if cand not in used:
            used.add(cand)
            return cand


def _parse_dis_enum_to_attrs(enum_str: str) -> Dict[str, str]:

    parts = [p.strip() for p in str(enum_str).split(".")]
    keys = ["kind", "domain", "country", "category", "subcategory", "specific", "extra"]
    attrs = {}
    for k, v in zip(keys, parts):
        if v != "":
            attrs[k] = v
    return attrs


def import_dragon_xlsx_into_model(
    xlsx_path: str,
    model: Optional[ObsModel],
    unitlist_map: Optional[Dict[str, Dict[str, str]]] = None,
) -> ObsModel:

    import pandas as pd, math

    if model is None:
        model = _new_blank_model()
    # === Units from UNIT INFO ===
    try:
        unit_df = pd.read_excel(xlsx_path, sheet_name="UNIT INFO")
    except Exception as e:
        raise ValueError(f"Failed to read 'UNIT INFO' sheet: {e}")

    def val(x):
        if isinstance(x, float) and math.isnan(x):
            return None
        s = str(x).strip()
        return s if s else None

    used_ids: Set[str] = set()
    used_unit_ids: Set[str] = set()
    for u in list(model.unit_list):
        lid = text(jfind(u, "j:LvcId"))
        if lid:
            used_ids.add(lid)
    cols = {str(c).strip().upper(): c for c in unit_df.columns}
    cname_col = cols.get("NAME") or cols.get("UNIT NAME") or cols.get("TITLE")
    uclass_col = cols.get("UNIT CLASS") or cols.get("CLASS") or cols.get("UNITCLASS")
    echelon_col = cols.get("ECHELON")
    ms2525_col = cols.get("2525C") or cols.get("MILSTD2525C") or cols.get("2525")
    uid_col = cols.get("UID") or cols.get("UNIT UID") or cols.get("UNIT_ID")
    parent_uid_col = (
        cols.get("PARENT UID") or cols.get("PARENT_UID") or cols.get("PARENT")
    )
    side_col = cols.get("SIDE") or cols.get("SIDE SUPERIOR") or cols.get("SIDESUPERIOR")
    uid_to_lvc: Dict[str, str] = {}
    created_units: Dict[str, ET._Element] = {}
    for _, row in unit_df.iterrows():
        uid = val(row.get(uid_col)) if uid_col else None
        name = val(row.get(cname_col)) if cname_col else None
        if not name:
            continue
        lvc = _gen_unique_lvcid("U", used_ids)
        u = ET.SubElement(model.unit_list, jtag("Unit"))
        u.set("id", _gen_unit_xml_id(used_unit_ids))
        u.set("dateTimeStamp", _now_iso_seconds_no_tz())
        ET.SubElement(u, jtag("LvcId")).text = lvc
        ET.SubElement(u, jtag("Name")).text = _sanitize_unit_name(name)
        if side_col:
            sv = val(row.get(side_col))
            if sv:
                ET.SubElement(u, jtag("SideSuperior")).text = sv
        if uclass_col:
            clsname = val(row.get(uclass_col))
            if clsname:
                ET.SubElement(u, jtag("ClassName")).text = clsname
        if echelon_col:
            ech = _expand_echelon(val(row.get(echelon_col)))
            if ech:
                ET.SubElement(u, jtag("Echelon")).text = ech
        if ms2525_col:
            code2525 = val(row.get(ms2525_col))
            if code2525:
                ET.SubElement(u, jtag("MilStd2525CCode")).text = code2525
                # Look up and inject UnitDisEnumeration from reference map
                if unitlist_map is not None:
                    attrs = unitlist_map.get(code2525) or unitlist_map.get(
                        code2525.upper()
                    )
                    if attrs:
                        ude = ET.SubElement(u, jtag("UnitDisEnumeration"))
                        for k, v in attrs.items():
                            ude.set(k, str(v))
        own = ET.SubElement(u, jtag("OwningFederate"))
        ET.SubElement(own, jtag("Federate")).text = "WARSIM"
        ET.SubElement(u, jtag("IsInactive")).text = "false"
        ET.SubElement(u, jtag("Strength")).text = "100"
        ET.SubElement(u, jtag("IsAggCommandable")).text = "false"
        if uid:
            uid_to_lvc[uid] = lvc
        created_units[lvc] = u
    if parent_uid_col and uid_col:
        for _, row in unit_df.iterrows():
            uid = val(row.get(uid_col))
            parent_uid = val(row.get(parent_uid_col))
            if not uid:
                continue
            child_lvc = uid_to_lvc.get(uid)
            if not child_lvc:
                continue
            child_unit = created_units.get(child_lvc)
            if child_unit is None:
                continue
            if parent_uid and parent_uid in uid_to_lvc:
                ET.SubElement(child_unit, jtag("UnitSuperior")).text = uid_to_lvc[
                    parent_uid
                ]
    # === EntityCompositions from other sheets ===
    xls = pd.ExcelFile(xlsx_path)
    for sheet in xls.sheet_names:
        if sheet.strip().upper() == "UNIT INFO":
            continue
        try:
            df = pd.read_excel(xlsx_path, sheet_name=sheet)
        except Exception:
            continue
        cols2 = {str(c).strip().upper(): c for c in df.columns}
        uidc = cols2.get("UID") or cols2.get("UNIT UID") or cols2.get("UNIT_ID")
        if not uidc:
            continue
        for _, row in df.iterrows():
            uid = val(row.get(uidc))
            if not uid:
                continue
            unit_lvc = uid_to_lvc.get(uid)
            if not unit_lvc:
                continue
            # Determine personnel
            is_person = False
            ptyp_col = cols2.get("PERSONNEL TYPE") or cols2.get("PERSONNEL TYPE CODE")
            if ptyp_col:
                ptyp = val(row.get(ptyp_col))
                is_person = bool(ptyp)
            ec = ET.SubElement(model.entcomp_list, jtag("EntityComposition"))
            ET.SubElement(ec, jtag("LvcId")).text = _gen_unique_lvcid("E", used_ids)
            ET.SubElement(ec, jtag("UnitSuperior")).text = unit_lvc
            ecc = ET.SubElement(ec, jtag("EntityCompositionClass"))
            cname = None
            if is_person and ptyp_col:
                cname = val(row.get(ptyp_col))
            else:
                eq_col = (
                    cols2.get("EQUIPMENT TYPE")
                    or cols2.get("EQUIP TYPE")
                    or cols2.get("TYPE")
                )
                cname = val(row.get(eq_col)) if eq_col else None
            if cname:
                ET.SubElement(ecc, jtag("ClassName")).text = cname
            dnode = ET.SubElement(ecc, jtag("DisCode"))
            den_col = cols2.get("DIS ENUMERATION") or cols2.get("DIS ENUM")
            den = val(row.get(den_col)) if den_col else None
            if den:
                attrs = _parse_dis_enum_to_attrs(den)
                for k, v in attrs.items():
                    dnode.set(k, str(v))
                if is_person and "kind" not in attrs:
                    dnode.set("kind", "3")
            else:
                dnode.set("kind", "3" if is_person else "1")
    return model


# ---------------- ClassData builders (from master spreadsheets) ----------------


def build_entitycomposition_classlist_from_xlsx(
    model: ObsModel, ecc_xlsx_path: str
) -> int:

    try:
        df = pd.read_excel(ecc_xlsx_path)
    except Exception as e:
        raise ValueError(f"Failed to read ECC master: {e}")
    cols = {c.strip().upper(): c for c in df.columns}
    plat_col = cols.get("PLATFORM") or list(df.columns)[0]
    dis_col = (
        cols.get("DIS ENUMERATION") or cols.get("DIS_ENUMERATION") or cols.get("DIS")
    )
    lst = jfind(model.classdata, "j:EntityCompositionClassList")
    if lst is None:
        lst = ET.SubElement(model.classdata, jtag("EntityCompositionClassList"))
    existing: Dict[str, List[ET._Element]] = {}
    for child in list(lst):
        name_text = text(jfind(child, "j:Name"))
        if not name_text:
            continue
        existing.setdefault(name_text.strip().upper(), []).append(child)
    new_entries: Dict[str, ET._Element] = {}
    tname_col = cols.get("TYPE NAME") or cols.get("TYPENAME") or None
    for _, row in df.iterrows():
        raw_name = row.get(plat_col)
        if raw_name is None or pd.isna(raw_name):
            continue
        name = str(raw_name).strip()
        if not name:
            continue
        raw_enum = row.get(dis_col)
        if raw_enum is None or pd.isna(raw_enum):
            continue
        enum = str(raw_enum).strip()
        if not enum:
            continue
        key = name.upper()
        prior = existing.pop(key, None)
        if prior:
            for elem in prior:
                lst.remove(elem)
        replacing = new_entries.pop(key, None)
        if replacing is not None:
            lst.remove(replacing)
        ecc = ET.SubElement(lst, jtag("EntityCompositionClass"))
        new_entries[key] = ecc
        ET.SubElement(ecc, jtag("Name")).text = name
        attrs = _parse_dis_enum_to_attrs(enum)
        dc = ET.SubElement(ecc, jtag("DisCode"))
        for k, v in attrs.items():
            dc.set(k, str(v))
        ET.SubElement(ecc, jtag("IsBaseClass")).text = "false"
        if tname_col:
            raw_tname = row.get(tname_col)
            if raw_tname is not None and pd.isna(raw_tname):
                raw_tname = None
            tname_val = str(raw_tname).strip() if raw_tname is not None else ""
            if tname_val:
                alias_list = ET.SubElement(ecc, jtag("AliasList"))
                alias = ET.SubElement(alias_list, jtag("Alias"))
                ET.SubElement(alias, jtag("Federate")).text = "WARSIM"
                ET.SubElement(alias, jtag("TypeName")).text = tname_val
    return len(new_entries)


def build_unitclass_list_from_xlsx(model: ObsModel, ucl_xlsx_path: str) -> int:

    try:
        df = pd.read_excel(ucl_xlsx_path)
    except Exception as e:
        raise ValueError(f"Failed to read UnitClass master: {e}")
    cols = {c.strip().upper(): c for c in df.columns}
    uclass_col = cols.get("UNIT CLASS") or list(df.columns)[0]
    tname_col = cols.get("TYPE NAME")
    code_col = cols.get("2525C") or cols.get("MILSTD2525C") or cols.get("MILSTD 2525C")
    lst = jfind(model.classdata, "j:UnitClassList")
    if lst is None:
        lst = ET.SubElement(model.classdata, jtag("UnitClassList"))
    existing: Dict[str, List[ET._Element]] = {}
    for child in list(lst):
        agg = text(jfind(child, "j:AggregateName"))
        if not agg:
            continue
        existing.setdefault(agg.strip().upper(), []).append(child)
    new_entries: Dict[str, ET._Element] = {}
    den_col = cols.get("DIS ENUMERATION") or cols.get("DIS_ENUMERATION")
    for _, row in df.iterrows():
        raw_name = row.get(uclass_col)
        if raw_name is None or pd.isna(raw_name):
            continue
        cname = str(raw_name).strip()
        if not cname:
            continue
        raw_tname = row.get(tname_col) if tname_col else None
        if raw_tname is not None and pd.isna(raw_tname):
            raw_tname = None
        tname = str(raw_tname).strip() if raw_tname is not None else ""
        raw_code = row.get(code_col) if code_col else None
        if raw_code is not None and pd.isna(raw_code):
            raw_code = None
        code2525 = str(raw_code).strip() if raw_code is not None else ""
        key = cname.upper()
        prior = existing.pop(key, None)
        if prior:
            for elem in prior:
                lst.remove(elem)
        replacing = new_entries.pop(key, None)
        if replacing is not None:
            lst.remove(replacing)
        ucl = ET.SubElement(lst, jtag("UnitClass"))
        new_entries[key] = ucl
        ET.SubElement(ucl, jtag("AggregateName")).text = cname
        if code2525:
            ET.SubElement(ucl, jtag("MilStd2525CCode")).text = code2525
        if den_col:
            raw_enum = row.get(den_col)
            if raw_enum is not None and pd.isna(raw_enum):
                raw_enum = None
            enum_val = str(raw_enum).strip() if raw_enum is not None else ""
            if enum_val:
                attrs = _parse_dis_enum_to_attrs(enum_val)
                ude = ET.SubElement(ucl, jtag("UnitDisEnumeration"))
                for k, v in attrs.items():
                    ude.set(k, str(v))
        if tname:
            alias_list = ET.SubElement(ucl, jtag("AliasList"))
            alias = ET.SubElement(alias_list, jtag("Alias"))
            ET.SubElement(alias, jtag("Federate")).text = "WARSIM"
            ET.SubElement(alias, jtag("TypeName")).text = tname
    return len(new_entries)


class AnalyzerTab(QWidget):

    modelLoaded = pyqtSignal(object)

    def __init__(self, parent):
        super().__init__(parent)
        self.model: Optional[ObsModel] = None
        self._build()

    def _build(self):
        lay = QVBoxLayout(self)
        src_box = QHBoxLayout()
        self.path_edit = QLineEdit()
        self.path_edit.setPlaceholderText("Select a JTDS OBS .xml or .zip ...")
        btn_browse = QPushButton("Open...")
        btn_browse.clicked.connect(self.on_browse)
        src_box.addWidget(self.path_edit)
        src_box.addWidget(btn_browse)
        lay.addLayout(src_box)
        self.summary = QTextEdit()
        self.summary.setReadOnly(True)
        self.summary.setMinimumHeight(200)
        lay.addWidget(self.summary)
        self.btn_analyze = QPushButton("Analyze")
        self.btn_analyze.clicked.connect(self.on_analyze)
        self.btn_analyze.setEnabled(False)
        lay.addWidget(self.btn_analyze, alignment=Qt.AlignmentFlag.AlignRight)

    def set_model(self, model: Optional[ObsModel]):
        self.model = model
        self.btn_analyze.setEnabled(model is not None)

    def on_browse(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open JTDS OBS", "", "OBS XML or ZIP (*.xml *.zip);;All Files (*)"
        )
        if path:
            self.path_edit.setText(path)
            try:
                model = load_obs_xml(path)
                self.set_model(model)
                self.summary.setPlainText(
                    "Loaded. Click Analyze to compute statistics."
                )
                self.modelLoaded.emit(model)
            except Exception as e:
                traceback.print_exc()
                QMessageBox.critical(self, "Open Error", str(e))

    def on_analyze(self):
        if not self.model:
            return
        m = self.model
        units = len(list(m.unit_list))
        total_ecs = len(list(m.entcomp_list))
        pers = count_personnel(m)
        equip = total_ecs - pers
        # Branch presence
        id_to_unit, _ = collect_unit_maps(m)
        found = {b: 0 for b in BRANCH_TOKENS}
        for u in id_to_unit.values():
            b = unit_branch(u)
            if b:
                found[b] += 1
        lines = []
        lines.append(f"Units: {units:,}")
        lines.append(f"Entity Compositions (Equipment): {equip:,}")
        lines.append(f"Personnel (DisCode kind=3): {pers:,}")
        lines.append("")
        lines.append("Parent unit branches present:")
        for key in ["SIG", "MNT", "ENG", "MED", "SPT", "CHEM"]:
            lines.append(f"  {key}: {'Yes' if found[key] else 'No'} ({found[key]})")
        self.summary.setPlainText("\\n".join(lines))


class ScrubberTab(QWidget):

    def __init__(self, parent):
        super().__init__(parent)
        self.model: Optional[ObsModel] = None
        self._build()

    def _build(self):
        lay = QVBoxLayout(self)
        form = QGridLayout()
        self.chk_supply = QCheckBox("Remove <SupplyClassList>")
        self.chk_emitter = QCheckBox("Remove <EmitterClassList>")
        self.chk_munit = QCheckBox("Remove <MunitionsList>")
        self.chk_fly = QCheckBox("Remove <FlyOutList>")
        self.chk_personnel = QCheckBox("Remove Personnel (DisCode kind=3)")
        self.chk_munitions_kind2 = QCheckBox("Remove Munitions (DisCode kind=2)")
        self.chk_remove_unused_ecc = QCheckBox(
            "Remove unused EntityCompositionClass entries"
        )
        self.chk_report_missing_ecc = QCheckBox(
            "Report EntityComposition ClassName mismatches"
        )
        row = 0
        toggles = [
            self.chk_supply,
            self.chk_emitter,
            self.chk_munit,
            self.chk_fly,
            self.chk_personnel,
            self.chk_munitions_kind2,
            self.chk_remove_unused_ecc,
            self.chk_report_missing_ecc,
        ]
        for w in toggles:
            form.addWidget(w, row, 0)
            row += 1
        # Branch group
        grp = QGroupBox("Remove Units by Branch (and their equipment/personnel)")
        grp_l = QHBoxLayout(grp)
        self.chk_SIG = QCheckBox("SIG")
        self.chk_MNT = QCheckBox("MNT")
        self.chk_ENG = QCheckBox("ENG")
        self.chk_MED = QCheckBox("MED")
        self.chk_SPT = QCheckBox("SPT")
        self.chk_CHEM = QCheckBox("CHEM")
        for w in [
            self.chk_SIG,
            self.chk_MNT,
            self.chk_ENG,
            self.chk_MED,
            self.chk_SPT,
            self.chk_CHEM,
        ]:
            grp_l.addWidget(w)
        lay.addLayout(form)
        lay.addWidget(grp)
        # Side removal
        side_box = QHBoxLayout()
        self.chk_side = QCheckBox("Remove side (units + ECs)")
        self.cmb_side = QComboBox()
        self.cmb_side.addItems(["OPFOR", "BLUFOR", "NEUTRAL", "CIVILIAN", "UNKNOWN"])
        side_box.addWidget(self.chk_side)
        side_box.addWidget(self.cmb_side)
        lay.addLayout(side_box)
        discode_box = QHBoxLayout()
        discode_box.addWidget(QLabel("Remove by DisCode:"))
        self.discode_edit = QLineEdit()
        self.discode_edit.setPlaceholderText("e.g. 1.1.225.28.1.0.0")
        self.discode_edit.setEnabled(False)
        discode_box.addWidget(self.discode_edit)
        self.btn_remove_discode = QPushButton("Remove")
        self.btn_remove_discode.setEnabled(False)
        self.btn_remove_discode.clicked.connect(self.on_remove_discode)
        discode_box.addWidget(self.btn_remove_discode)
        lay.addLayout(discode_box)
        replace_box = QHBoxLayout()
        replace_box.addWidget(QLabel("Replace DisCode:"))
        self.discode_replace_from_edit = QLineEdit()
        self.discode_replace_from_edit.setPlaceholderText(
            "Current e.g. 1.1.225.28.1.0.0"
        )
        self.discode_replace_from_edit.setEnabled(False)
        replace_box.addWidget(self.discode_replace_from_edit)
        replace_box.addWidget(QLabel("to"))
        self.discode_replace_to_edit = QLineEdit()
        self.discode_replace_to_edit.setPlaceholderText("New e.g. 1.1.225.28.2.0.0")
        self.discode_replace_to_edit.setEnabled(False)
        replace_box.addWidget(self.discode_replace_to_edit)
        self.btn_replace_discode = QPushButton("Replace")
        self.btn_replace_discode.setEnabled(False)
        self.btn_replace_discode.clicked.connect(self.on_replace_discode)
        replace_box.addWidget(self.btn_replace_discode)
        lay.addLayout(replace_box)
        self.btn_apply = QPushButton("Apply Scrub")
        self.btn_apply.clicked.connect(self.on_apply)
        self.btn_apply.setEnabled(False)
        lay.addWidget(self.btn_apply, alignment=Qt.AlignmentFlag.AlignRight)
        self.out = QTextEdit()
        self.out.setReadOnly(True)
        self.out.setMinimumHeight(180)
        lay.addWidget(self.out)

    def set_model(self, model: Optional[ObsModel]):
        self.model = model
        enabled = model is not None
        self.btn_apply.setEnabled(enabled)
        self.discode_edit.setEnabled(enabled)
        self.btn_remove_discode.setEnabled(enabled)
        self.discode_replace_from_edit.setEnabled(enabled)
        self.discode_replace_to_edit.setEnabled(enabled)
        self.btn_replace_discode.setEnabled(enabled)
        if not enabled:
            self.discode_edit.clear()
            self.discode_replace_from_edit.clear()
            self.discode_replace_to_edit.clear()
            return
        sides = set()
        for u in list(model.unit_list):
            ss = text(jfind(u, "j:SideSuperior"))
            if ss:
                sides.add(ss.strip())
        for s in sorted(sides):
            if self.cmb_side.findText(s) == -1:
                self.cmb_side.addItem(s)

    def on_apply(self):
        if not self.model:
            return
        m = self.model
        report = []
        counts = purge_classdata_sections(
            m,
            supply=self.chk_supply.isChecked(),
            emitter=self.chk_emitter.isChecked(),
            munitions=self.chk_munit.isChecked(),
            flyout=self.chk_fly.isChecked(),
        )
        for k, v in counts.items():
            report.append(f"Removed {k}: {v} entries")
        if self.chk_personnel.isChecked():
            rem_ec, rem_ecc = remove_personnel(m)
            report.append(
                f"Removed Personnel (kind=3): ECs={rem_ec}, Classes={rem_ecc}"
            )
        if (
            getattr(self, "chk_munitions_kind2", None)
            and self.chk_munitions_kind2.isChecked()
        ):
            rem_ec, rem_ecc = remove_munitions(m)
            report.append(
                f"Removed Munitions (kind=2): ECs={rem_ec}, Classes={rem_ecc}"
            )
        branches = set()
        for key, chk in [
            ("SIG", self.chk_SIG),
            ("MNT", self.chk_MNT),
            ("ENG", self.chk_ENG),
            ("MED", self.chk_MED),
            ("SPT", self.chk_SPT),
            ("CHEM", self.chk_CHEM),
        ]:
            if chk.isChecked():
                branches.add(key)
        if branches:
            ru, re = remove_units_by_branch(m, branches)
            report.append(
                f"Removed Units by Branch {sorted(list(branches))}: Units={ru}, EntityCompositions={re}"
            )
        if self.chk_side.isChecked():
            side = self.cmb_side.currentText() or "OPFOR"
            ru2, re2 = remove_side(m, side)
            report.append(f"Removed side {side}: Units={ru2}, EntityCompositions={re2}")
        if (
            getattr(self, "chk_remove_unused_ecc", None)
            and self.chk_remove_unused_ecc.isChecked()
        ):
            removed_ecc, removed_labels, unnamed_removed = (
                remove_unused_entity_composition_classes(m)
            )
            if removed_ecc:
                details: List[str] = []
                if removed_labels:
                    preview = ", ".join(removed_labels[:10])
                    if len(removed_labels) > 10:
                        preview += f", +{len(removed_labels) - 10} more"
                    details.append(f"labels: {preview}")
                if unnamed_removed:
                    details.append(f"{unnamed_removed} unnamed")
                suffix = f" ({', '.join(details)})" if details else ""
                report.append(
                    f"Removed unused EntityCompositionClass entries: {removed_ecc}{suffix}"
                )
            else:
                report.append("No unused EntityCompositionClass entries detected.")
        if (
            getattr(self, "chk_report_missing_ecc", None)
            and self.chk_report_missing_ecc.isChecked()
        ):
            missing = find_missing_entity_composition_classes(m)
            if missing:
                preview = ", ".join(missing[:10])
                if len(missing) > 10:
                    preview += f", +{len(missing) - 10} more"
                report.append(
                    f"Missing {len(missing)} EntityCompositionClass definition(s) for: {preview}"
                )
            else:
                report.append(
                    "All EntityComposition <ClassName> values have matching EntityCompositionClass entries."
                )
        if not report:
            report.append("No changes selected.")
        self.out.setPlainText("\\n".join(report))

    def on_replace_discode(self):
        if not self.model:
            QMessageBox.warning(
                self, "Replace DisCode", "Load a model before replacing entities."
            )
            return
        old = (self.discode_replace_from_edit.text() or "").strip()
        new = (self.discode_replace_to_edit.text() or "").strip()
        if not old:
            QMessageBox.warning(
                self,
                "Replace DisCode",
                "Enter the DisCode value to replace (e.g. 1.1.225.28.1.0.0).",
            )
            self.discode_replace_from_edit.setFocus()
            return
        if not new:
            QMessageBox.warning(self, "Replace DisCode", "Enter the new DisCode value.")
            self.discode_replace_to_edit.setFocus()
            return
        try:
            updated_ecc, updated_entities = replace_discode_entries(
                self.model, old, new
            )
        except ValueError as exc:
            QMessageBox.warning(self, "Replace DisCode", str(exc))
            return
        if updated_ecc == 0 and updated_entities == 0:
            QMessageBox.information(
                self, "Replace DisCode", f"No entries matched DisCode {old}."
            )
            return
        self.out.append(
            f"Replaced DisCode {old} -> {new}: Classes={updated_ecc}, EntityCompositions={updated_entities}"
        )
        QMessageBox.information(
            self,
            "Replace DisCode",
            f"Replaced DisCode {old} -> {new}: Classes={updated_ecc}, EntityCompositions={updated_entities}",
        )
        self.discode_replace_from_edit.selectAll()

    def on_remove_discode(self):
        if not self.model:
            QMessageBox.warning(
                self, "Remove by DisCode", "Load a model before removing entities."
            )
            return
        code = (self.discode_edit.text() or "").strip()
        if not code:
            QMessageBox.warning(
                self,
                "Remove by DisCode",
                "Enter a DisCode value (e.g. 1.1.225.28.1.0.0).",
            )
            self.discode_edit.setFocus()
            return
        try:
            removed_ec, removed_ecc = remove_entities_by_discode(self.model, code)
        except ValueError as exc:
            QMessageBox.warning(self, "Remove by DisCode", str(exc))
            return
        if removed_ec == 0 and removed_ecc == 0:
            QMessageBox.information(
                self, "Remove by DisCode", f"No entities matched DisCode {code}."
            )
            return
        self.out.append(
            f"Removed DisCode {code}: EntityCompositions={removed_ec}, Classes={removed_ecc}"
        )
        QMessageBox.information(
            self,
            "Remove by DisCode",
            f"Removed DisCode {code}: EntityCompositions={removed_ec}, Classes={removed_ecc}",
        )
        self.discode_edit.selectAll()


class ModelPreviewDialog(QDialog):

    SIDE_ORDER = list(DEFAULT_SIDE_ORDER)

    def __init__(self, parent: Optional[QWidget] = None):
        super().__init__(parent)
        self._model: Optional[ObsModel] = None
        self._last_consolidation_label: Optional[str] = None
        self.setWindowTitle("Model Hierarchy Preview")
        self.resize(720, 560)
        layout = QVBoxLayout(self)
        search_row = QHBoxLayout()
        search_row.addWidget(QLabel("Filter:"))
        self._filter_edit = QLineEdit()
        self._filter_edit.setPlaceholderText(
            "Type to filter by name, role, or LvcId..."
        )
        search_row.addWidget(self._filter_edit)
        self._clear_filter_btn = QPushButton("Clear")
        self._clear_filter_btn.setAutoDefault(False)
        self._clear_filter_btn.clicked.connect(self._clear_filter)
        search_row.addWidget(self._clear_filter_btn)
        search_row.addStretch()
        layout.addLayout(search_row)
        self._filter_edit.textChanged.connect(self._on_filter_changed)
        self.tree = QTreeWidget()
        self.tree.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.tree.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self._on_tree_context_menu)
        self.tree.setColumnCount(2)
        self.tree.setHeaderLabels(["Name / Role", "2525C"])
        self.tree.setAlternatingRowColors(True)
        header = self.tree.header()
        header.setStretchLastSection(False)
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        layout.addWidget(self.tree)
        btn_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Close)
        self._export_btn = btn_box.addButton(
            "Export to Excel...", QDialogButtonBox.ButtonRole.ActionRole
        )
        self._export_btn.setAutoDefault(False)
        self._export_btn.clicked.connect(self._on_export_excel)
        btn_box.rejected.connect(self.reject)
        layout.addWidget(btn_box)

    def set_model(self, model: Optional[ObsModel]) -> None:
        self._model = model
        self.tree.clear()
        if model is None:
            return
        lvc_to_unit, parent_to_children = collect_unit_maps(model)
        ec_by_superior: Dict[str, List[ET._Element]] = {}
        orphan_ec: Dict[str, List[Tuple[ET._Element, str]]] = {}
        side_labels: Dict[str, str] = {}
        for ec in _iter_local(model.entcomp_list, "EntityComposition"):
            sup = (text(jfind(ec, "j:UnitSuperior")) or "").strip()
            if sup and sup in lvc_to_unit:
                ec_by_superior.setdefault(sup, []).append(ec)
            else:
                side_name = (text(jfind(ec, "j:SideSuperior")) or "").strip()
                side_key = side_name.upper() if side_name else "UNKNOWN"
                if side_name:
                    side_labels.setdefault(side_key, side_name)
                orphan_ec.setdefault(side_key, []).append((ec, sup))
        units = list(_iter_local(model.unit_list, "Unit"))
        side_roots: Dict[str, List[ET._Element]] = {}

        def unit_side(unit: ET._Element) -> str:
            raw = (text(jfind(unit, "j:SideSuperior")) or "").strip()
            if raw:
                key = raw.upper()
                side_labels.setdefault(key, raw)
                return key
            derived = _resolve_unit_side(unit, lvc_to_unit)
            if derived:
                key = derived.upper()
                side_labels.setdefault(key, derived)
                return key
            side_labels.setdefault("UNKNOWN", "UNKNOWN")
            return "UNKNOWN"

        for unit in units:
            side_key = unit_side(unit)
            parent = (text(jfind(unit, "j:UnitSuperior")) or "").strip()
            if not parent or parent not in lvc_to_unit:
                side_roots.setdefault(side_key, []).append(unit)
        all_sides = set(side_labels) | set(side_roots) | set(orphan_ec)
        if not all_sides:
            all_sides.add("UNKNOWN")
            side_labels.setdefault("UNKNOWN", "UNKNOWN")
        side_items: Dict[str, QTreeWidgetItem] = {}
        for side_key in sorted(all_sides, key=side_sort_key):
            self._ensure_side_item(side_key, side_labels, side_items)
        visited_units: Set[int] = set()
        for side_key, roots in side_roots.items():
            parent_item = self._ensure_side_item(side_key, side_labels, side_items)
            for unit in sorted(roots, key=self._unit_sort_key):
                self._add_unit_recursive(
                    unit,
                    parent_item,
                    lvc_to_unit,
                    parent_to_children,
                    ec_by_superior,
                    visited_units,
                )
        leftovers = [u for u in units if id(u) not in visited_units]
        if leftovers:
            side_item = self._ensure_side_item("UNKNOWN", side_labels, side_items)
            placeholder = QTreeWidgetItem(["Detached Units", ""])
            side_item.addChild(placeholder)
            for unit in sorted(leftovers, key=self._unit_sort_key):
                self._add_unit_recursive(
                    unit,
                    placeholder,
                    lvc_to_unit,
                    parent_to_children,
                    ec_by_superior,
                    visited_units,
                )
        for side_key, entries in orphan_ec.items():
            side_item = self._ensure_side_item(side_key, side_labels, side_items)
            orphan_parent = QTreeWidgetItem(["Entity Compositions (unattached)", ""])
            side_item.addChild(orphan_parent)
            for ec, sup in sorted(
                entries, key=lambda pair: self._entity_sort_key(pair[0])
            ):
                label = self._format_entity_label(
                    ec, include_superior=True, superior_hint=sup
                )
                code = (text(jfind(ec, "j:MilStd2525CCode")) or "").strip()
                item = QTreeWidgetItem([label, code])
                item.setData(0, Qt.ItemDataRole.UserRole, ("entity", ec))
                orphan_parent.addChild(item)
        current_filter = (self._filter_edit.text() or "").strip().lower()
        if current_filter:
            self._apply_filter(current_filter)
        else:
            self.tree.expandToDepth(0)

    def _clear_filter(self) -> None:
        if hasattr(self, "_filter_edit"):
            self._filter_edit.blockSignals(True)
            self._filter_edit.clear()
            self._filter_edit.blockSignals(False)
        self._apply_filter("")

    def _on_filter_changed(self, text: str) -> None:
        term = (text or "").strip().lower()
        self._apply_filter(term)

    def _apply_filter(self, term: str) -> None:
        if not term:
            for i in range(self.tree.topLevelItemCount()):
                item = self.tree.topLevelItem(i)
                self._set_hidden_recursive(item, False)
            self.tree.collapseAll()
            self.tree.expandToDepth(0)
            return
        for i in range(self.tree.topLevelItemCount()):
            item = self.tree.topLevelItem(i)
            visible = self._filter_item_recursive(item, term)
            item.setHidden(not visible)
        self.tree.expandAll()

    def _on_export_excel(self) -> None:
        if self._model is None:
            QMessageBox.information(
                self, "Export Preview", "Load a model before exporting the preview."
            )
            return
        rows = self._collect_tree_rows(include_hidden=True)
        if not rows:
            QMessageBox.information(
                self, "Export Preview", "The preview tree is empty."
            )
            return
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        suggested = f"ModelPreview_{timestamp}"
        path, _ = QFileDialog.getSaveFileName(
            self, "Export Preview to Excel", suggested, "Excel Workbook (*.xlsx)"
        )
        if not path:
            return
        if not path.lower().endswith(".xlsx"):
            path += ".xlsx"
        try:
            self._write_preview_excel(path, rows)
        except ImportError:
            QMessageBox.critical(
                self,
                "Export Preview",
                "openpyxl is required to export Excel files. Install openpyxl and try again.",
            )
        except Exception as exc:
            traceback.print_exc()
            QMessageBox.critical(
                self, "Export Preview", f"Failed to export preview: {exc}"
            )
        else:
            QMessageBox.information(
                self, "Export Preview", f"Preview exported to:\n{path}"
            )

    def _on_tree_context_menu(self, pos) -> None:
        item = self.tree.itemAt(pos)
        if item is None:
            return
        if not item.isSelected():
            self.tree.clearSelection()
            item.setSelected(True)
        selected_items: List[Tuple[str, ET._Element]] = []
        for candidate in self.tree.selectedItems():
            data = candidate.data(0, Qt.ItemDataRole.UserRole)
            if isinstance(data, tuple) and data:
                kind = data[0]
                if kind in ("unit", "entity"):
                    selected_items.append(data)
        if not selected_items:
            return
        units = [data for data in selected_items if data[0] == "unit"]
        entities = [data for data in selected_items if data[0] == "entity"]
        menu = QMenu(self)
        rename_action = None
        move_action = None
        if len(selected_items) == 1:
            kind, _ = selected_items[0]
            if kind == "unit":
                rename_action = menu.addAction("Rename unit...")
                move_action = menu.addAction("Move unit...")
            elif kind == "entity":
                rename_action = menu.addAction("Rename entity composition...")
                move_action = menu.addAction("Move entity to unit...")
            if rename_action or move_action:
                menu.addSeparator()
        delete_action = None
        consolidate_action = None
        if units or entities:
            if units and entities:
                delete_text = f"Delete {len(units)} unit(s) and {len(entities)} entity composition(s)"
            elif units:
                delete_text = (
                    "Delete selected unit"
                    if len(units) == 1
                    else f"Delete {len(units)} units and subordinates"
                )
            else:
                delete_text = (
                    "Delete selected entity composition"
                    if len(entities) == 1
                    else f"Delete {len(entities)} entity compositions"
                )
            delete_action = menu.addAction(delete_text)
        if units:
            if len(units) == 1:
                consolidate_text = "Consolidate subtree into this unit..."
            else:
                consolidate_text = (
                    f"Consolidate {len(units)} units into selected level..."
                )
            consolidate_action = menu.addAction(consolidate_text)
            if entities:
                consolidate_action.setEnabled(False)
        chosen = menu.exec(self.tree.viewport().mapToGlobal(pos))
        if chosen is None:
            return
        if rename_action is not None and chosen == rename_action:
            self._handle_rename_request(selected_items[0])
            return
        if move_action is not None and chosen == move_action:
            self._handle_move_request(selected_items[0])
            return
        if delete_action is not None and chosen == delete_action:
            self._handle_delete_request(selected_items)
            return
        if (
            consolidate_action is not None
            and chosen == consolidate_action
            and (
                consolidate_action.isEnabled()
                if hasattr(consolidate_action, "isEnabled")
                else not entities
            )
        ):
            self._handle_consolidate_subtree([data[1] for data in units])

    def _handle_delete_request(self, payload) -> None:
        if self._model is None:
            return
        if isinstance(payload, list):
            raw_items = payload
        elif isinstance(payload, tuple):
            raw_items = [payload]
        elif payload is None:
            raw_items = []
        else:
            raw_items = list(payload)
        unique_payloads = []
        seen = set()
        for entry in raw_items:
            if not isinstance(entry, tuple) or len(entry) < 2:
                continue
            kind, element = entry[0], entry[1]
            if kind not in ("unit", "entity"):
                continue
            key = (kind, id(element))
            if key in seen:
                continue
            seen.add(key)
            unique_payloads.append((kind, element))
        if not unique_payloads:
            return
        changed = False
        unit_targets = []
        skipped_units = []
        for kind, element in unique_payloads:
            if kind != "unit":
                continue
            lvc = (text(jfind(element, "j:LvcId")) or "").strip()
            if not lvc:
                skipped_units.append(self._format_unit_label(element))
                continue
            unit_targets.append((element, lvc))
        if unit_targets:
            labels = [self._format_unit_label(elem) for elem, _ in unit_targets]
            if len(labels) == 1:
                prompt = f"Delete unit '{labels[0]}' and all subordinate units and entity compositions?"
            else:
                preview = ", ".join(labels[:5])
                if len(labels) > 5:
                    preview += ", ..."
                prompt = f"Delete {len(labels)} units and all subordinate units and entity compositions?\n\nExamples: {preview}"
            confirm = QMessageBox.question(
                self,
                "Confirm Deletion",
                prompt,
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if confirm == QMessageBox.StandardButton.Yes:
                removed_units = 0
                removed_ecs = 0
                for _, lvc in unit_targets:
                    ru, re = remove_unit_subtree(self._model, lvc)
                    removed_units += ru
                    removed_ecs += re
                if removed_units == 0 and removed_ecs == 0:
                    QMessageBox.information(
                        self, "Delete Unit", "No units were removed."
                    )
                else:
                    changed = True
        if skipped_units:
            message = (
                "The following units do not have an LvcId and were skipped:\n"
                + "\n".join(skipped_units[:10])
            )
            if len(skipped_units) > 10:
                message += "\n..."
            QMessageBox.warning(self, "Delete Unit", message)
        entity_targets = [
            element for kind, element in unique_payloads if kind == "entity"
        ]
        if entity_targets:
            labels = [self._format_entity_label(elem) for elem in entity_targets]
            if len(labels) == 1:
                prompt = f"Delete entity composition '{labels[0]}'?"
            else:
                preview = ", ".join(labels[:5])
                if len(labels) > 5:
                    preview += ", ..."
                prompt = (
                    f"Delete {len(labels)} entity compositions?\n\nExamples: {preview}"
                )
            confirm = QMessageBox.question(
                self,
                "Confirm Deletion",
                prompt,
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if confirm == QMessageBox.StandardButton.Yes:
                removed = 0
                missing = []
                for elem in entity_targets:
                    try:
                        self._model.entcomp_list.remove(elem)
                        removed += 1
                    except ValueError:
                        missing.append(self._format_entity_label(elem))
                if removed:
                    changed = True
                if missing:
                    detail = "\n".join(missing[:10])
                    if len(missing) > 10:
                        detail += "\n..."
                    QMessageBox.information(
                        self,
                        "Delete Entity Composition",
                        "Some entity compositions were not found and could not be removed:\n"
                        + detail,
                    )
        if changed:
            self.set_model(self._model)

    def _handle_rename_request(self, payload: Tuple[str, ET._Element]) -> None:
        if self._model is None:
            return
        kind, element = payload
        changed = False
        if kind == "unit":
            changed = self._rename_unit(element)
        elif kind == "entity":
            changed = self._rename_entity(element)
        if changed:
            self.set_model(self._model)

    def _rename_unit(self, unit_elem: ET._Element) -> bool:
        name_el = jfind(unit_elem, "j:Name")
        old_name = (
            (name_el.text or "").strip() if name_el is not None and name_el.text else ""
        )
        new_name, ok = QInputDialog.getText(
            self, "Rename Unit", "New unit name:", text=old_name
        )
        if not ok:
            return False
        new_name = (new_name or "").strip()
        if not new_name:
            QMessageBox.information(self, "Rename Unit", "Name cannot be empty.")
            return False
        if new_name == old_name:
            return False
        if name_el is None:
            name_el = ET.SubElement(unit_elem, jtag("Name"))
        name_el.text = new_name
        updated_children = 0
        old_base = ""
        if old_name:
            old_base, _ = _split_unit_name_components(old_name)
        new_base, _ = _split_unit_name_components(new_name)
        if old_base and new_base and old_base.upper() != new_base.upper():
            _, parent_to_children = collect_unit_maps(self._model)
            for descendant in _gather_unit_descendants(unit_elem, parent_to_children):
                name_node = jfind(descendant, "j:Name")
                if name_node is None or not name_node.text:
                    continue
                current_name = name_node.text.strip()
                child_base, child_suffix = _split_unit_name_components(current_name)
                if child_base and child_base.upper() == old_base.upper():
                    new_child = new_base
                    if child_suffix:
                        new_child = f"{new_base}_{child_suffix}"
                    name_node.text = new_child
                    updated_children += 1
        message = f"Renamed unit to '{new_name}'."
        if updated_children:
            message += f" Updated {updated_children} subordinate name(s)."
        QMessageBox.information(self, "Rename Unit", message)
        return True

    def _rename_entity(self, entity_elem: ET._Element) -> bool:
        role_el = jfind(entity_elem, "j:Role")
        old_role = (
            (role_el.text or "").strip() if role_el is not None and role_el.text else ""
        )
        new_role, ok = QInputDialog.getText(
            self, "Rename Entity Composition", "New role:", text=old_role
        )
        if not ok:
            return False
        new_role = (new_role or "").strip()
        if not new_role:
            QMessageBox.information(
                self, "Rename Entity Composition", "Role cannot be empty."
            )
            return False
        if new_role == old_role:
            return False
        if role_el is None:
            role_el = ET.SubElement(entity_elem, jtag("Role"))
        role_el.text = new_role
        name_el = jfind(entity_elem, "j:Name")
        if name_el is not None:
            name_el.text = new_role
        QMessageBox.information(
            self,
            "Rename Entity Composition",
            f"Renamed entity composition to '{new_role}'.",
        )
        return True

    def _handle_move_request(self, payload: Tuple[str, ET._Element]) -> None:
        if self._model is None:
            return
        kind, element = payload
        if kind == "unit":
            dialog = ObsMoveUnitDialog(
                self, self._model, blocked_units={element}, allow_side_selection=True
            )
        else:
            dialog = ObsMoveUnitDialog(
                self, self._model, blocked_units=set(), allow_side_selection=False
            )
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return
        target = dialog.selected_target()
        if target is None:
            return
        if kind == "unit":
            message = self._move_unit(element, target)
        else:
            message = self._move_entity(element, target)
        if message:
            QMessageBox.information(self, "Move", message)
        self.set_model(self._model)

    def _move_unit(self, unit_elem: ET._Element, target: Tuple[str, Any]) -> str:
        kind = target[0]
        label = self._format_unit_label(unit_elem)
        if kind == "unit":
            parent_unit = target[1]
            parent_lvc = (text(jfind(parent_unit, "j:LvcId")) or "").strip()
            if not parent_lvc:
                QMessageBox.warning(
                    self, "Move Unit", "Selected parent unit does not have an LvcId."
                )
                return ""
            current_sup = (text(jfind(unit_elem, "j:UnitSuperior")) or "").strip()
            if current_sup == parent_lvc:
                return "Unit is already assigned to the selected parent."
            sup_el = jfind(unit_elem, "j:UnitSuperior")
            if sup_el is None:
                sup_el = ET.SubElement(unit_elem, jtag("UnitSuperior"))
            sup_el.text = parent_lvc
            parent_label = self._format_unit_label(parent_unit)
            parent_side = (text(jfind(parent_unit, "j:SideSuperior")) or "").strip()
            updated = 0
            if parent_side:
                updated = self._apply_side_to_subtree(unit_elem, parent_side)
            message = f"Moved unit '{label}' under '{parent_label}'."
            if updated:
                message += f" Updated side '{parent_side}' on {updated} unit(s)."
            return message
        if kind == "side":
            side_key = target[1]
            side_display = target[2]
            sup_el = jfind(unit_elem, "j:UnitSuperior")
            if sup_el is not None:
                try:
                    unit_elem.remove(sup_el)
                except Exception:
                    sup_el.text = ""
            side_value = side_display or side_key
            updated = self._apply_side_to_subtree(unit_elem, side_value)
            return f"Moved unit '{label}' to side '{side_value}'. Updated side on {updated} unit(s)."
        QMessageBox.warning(self, "Move Unit", "Invalid destination selected.")
        return ""

    def _move_entity(self, entity_elem: ET._Element, target: Tuple[str, Any]) -> str:
        if target[0] != "unit":
            QMessageBox.warning(
                self, "Move Entity Composition", "Select a destination unit."
            )
            return ""
        parent_unit = target[1]
        parent_lvc = (text(jfind(parent_unit, "j:LvcId")) or "").strip()
        if not parent_lvc:
            QMessageBox.warning(
                self,
                "Move Entity Composition",
                "Selected destination unit does not have an LvcId.",
            )
            return ""
        sup_el = jfind(entity_elem, "j:UnitSuperior")
        if sup_el is None:
            sup_el = ET.SubElement(entity_elem, jtag("UnitSuperior"))
        sup_el.text = parent_lvc
        parent_side = (text(jfind(parent_unit, "j:SideSuperior")) or "").strip()
        if parent_side:
            side_el = jfind(entity_elem, "j:SideSuperior")
            if side_el is None:
                side_el = ET.SubElement(entity_elem, jtag("SideSuperior"))
            side_el.text = parent_side
        return (
            f"Moved entity composition under '{self._format_unit_label(parent_unit)}'."
        )

    def _apply_side_to_subtree(self, unit_elem: ET._Element, side_value: str) -> int:
        _, parent_to_children = collect_unit_maps(self._model)
        nodes = _gather_unit_descendants(
            unit_elem, parent_to_children, include_root=True
        )
        updated = 0
        for node in nodes:
            side_el = jfind(node, "j:SideSuperior")
            if not side_value:
                if side_el is not None:
                    try:
                        node.remove(side_el)
                    except Exception:
                        side_el.text = ""
                    updated += 1
                continue
            if side_el is None:
                side_el = ET.SubElement(node, jtag("SideSuperior"))
            if (side_el.text or "").strip() != side_value:
                side_el.text = side_value
                updated += 1
        return updated

    def _handle_consolidate_subtree(self, unit_elems) -> None:
        if self._model is None:
            return
        if isinstance(unit_elems, list):
            candidates = unit_elems
        elif isinstance(unit_elems, tuple):
            candidates = list(unit_elems)
        elif unit_elems is None:
            candidates = []
        else:
            candidates = [unit_elems]
        unique_units = []
        seen_ids = set()
        for unit in candidates:
            if unit is None:
                continue
            key = id(unit)
            if key in seen_ids:
                continue
            seen_ids.add(key)
            unique_units.append(unit)
        if not unique_units:
            return
        unit_targets = []
        skipped = []
        for unit in unique_units:
            lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
            if not lvc:
                skipped.append(self._format_unit_label(unit))
                continue
            unit_targets.append((unit, lvc))
        if not unit_targets:
            if skipped:
                message = (
                    "The selected unit does not have an LvcId."
                    if len(skipped) == 1
                    else "The selected units do not have LvcIds."
                )
                QMessageBox.warning(self, "Consolidate Subtree", message)
            return
        if skipped:
            detail = "\n".join(skipped[:10])
            if len(skipped) > 10:
                detail += "\n..."
            QMessageBox.warning(
                self,
                "Consolidate Subtree",
                "The following units are missing an LvcId and will be skipped:\n"
                + detail,
            )
        levels = CONSOLIDATION_LEVELS
        if not levels:
            QMessageBox.warning(
                self, "Consolidate Subtree", "No consolidation levels are available."
            )
            return
        default_label = self._last_consolidation_label or levels[0]
        try:
            default_index = levels.index(default_label)
        except ValueError:
            default_index = 0
        selection, ok = QInputDialog.getItem(
            self,
            "Consolidate Subtree",
            "Consolidate lower echelons up to:",
            levels,
            default_index,
            False,
        )
        if not ok:
            return
        target_label = (selection or "").strip()
        if not target_label:
            return
        self._last_consolidation_label = target_label
        scope_roots = {lvc for _, lvc in unit_targets}
        stats = consolidate_units(self._model, target_label, scope_roots=scope_roots)
        total_changes = (
            stats["removed_units"]
            + stats["moved_entity_compositions"]
            + stats["relinked_units"]
        )
        if total_changes == 0:
            message = (
                "No changes were made for the selected unit."
                if len(scope_roots) == 1
                else "No changes were made for the selected units."
            )
            QMessageBox.information(self, "Consolidate Subtree", message)
            return
        skipped_units = stats.get("skipped_units", 0)
        parts = [
            f"removed units {stats['removed_units']}",
            f"moved entity compositions {stats['moved_entity_compositions']}",
            f"relinked units {stats['relinked_units']}",
        ]
        if skipped_units:
            parts.append(f"skipped {skipped_units}")
        if len(unit_targets) == 1:
            label = self._format_unit_label(unit_targets[0][0])
            summary = f"Consolidated '{label}': " + ", ".join(parts)
        else:
            preview = ", ".join(
                self._format_unit_label(unit) for unit, _ in unit_targets[:5]
            )
            if len(unit_targets) > 5:
                preview += ", ..."
            summary = (
                f"Consolidated {len(unit_targets)} units: {preview}\n\nChanges: "
                + ", ".join(parts)
            )
        QMessageBox.information(self, "Consolidate Subtree", summary)
        self.set_model(self._model)

    def _set_hidden_recursive(self, item: QTreeWidgetItem, hidden: bool) -> None:
        item.setHidden(hidden)
        for i in range(item.childCount()):
            self._set_hidden_recursive(item.child(i), hidden)

    def _filter_item_recursive(self, item: QTreeWidgetItem, term: str) -> bool:
        current_match = any(
            term in (item.text(col) or "").lower() for col in range(item.columnCount())
        )
        child_match = False
        for i in range(item.childCount()):
            child = item.child(i)
            if self._filter_item_recursive(child, term):
                child_match = True
            else:
                child.setHidden(True)
        visible = current_match or child_match
        item.setHidden(not visible)
        return visible

    def _ensure_side_item(
        self,
        side_key: str,
        side_labels: Dict[str, str],
        side_items: Dict[str, QTreeWidgetItem],
    ) -> QTreeWidgetItem:
        item = side_items.get(side_key)
        if item is not None:
            return item
        display = side_labels.get(side_key, side_key)
        if side_key == "UNKNOWN" and display == "UNKNOWN":
            display = "UNKNOWN / Unassigned"
        item = QTreeWidgetItem([display, ""])
        item.setData(0, Qt.ItemDataRole.UserRole, side_key)
        self.tree.addTopLevelItem(item)
        side_items[side_key] = item
        return item

    def _add_unit_recursive(
        self,
        unit: ET._Element,
        parent_item: QTreeWidgetItem,
        lvc_to_unit: Dict[str, ET._Element],
        parent_to_children: Dict[str, List[ET._Element]],
        ec_by_superior: Dict[str, List[ET._Element]],
        visited_units: Set[int],
    ) -> None:
        if id(unit) in visited_units:
            return
        visited_units.add(id(unit))
        label = self._format_unit_label(unit)
        code = (text(jfind(unit, "j:MilStd2525CCode")) or "").strip()
        item = QTreeWidgetItem([label, code])
        item.setData(0, Qt.ItemDataRole.UserRole, ("unit", unit))
        parent_item.addChild(item)
        lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        for ec in sorted(ec_by_superior.get(lvc, []), key=self._entity_sort_key):
            self._add_entity_item(ec, item)
        for child in sorted(parent_to_children.get(lvc, []), key=self._unit_sort_key):
            self._add_unit_recursive(
                child,
                item,
                lvc_to_unit,
                parent_to_children,
                ec_by_superior,
                visited_units,
            )

    def _add_entity_item(self, ec: ET._Element, parent_item: QTreeWidgetItem) -> None:
        label = self._format_entity_label(ec)
        code = (text(jfind(ec, "j:MilStd2525CCode")) or "").strip()
        item = QTreeWidgetItem([label, code])
        item.setData(0, Qt.ItemDataRole.UserRole, ("entity", ec))
        parent_item.addChild(item)

    def _format_unit_label(self, unit: ET._Element) -> str:
        return format_unit_label(unit)

    def _format_entity_label(
        self,
        ec: ET._Element,
        *,
        include_superior: bool = False,
        superior_hint: Optional[str] = None,
    ) -> str:
        return format_entity_label(
            ec, include_superior=include_superior, superior_hint=superior_hint
        )

    def _unit_sort_key(self, unit: ET._Element) -> Tuple[int, str, str]:
        return unit_sort_key(unit)

    def _entity_sort_key(self, ec: ET._Element) -> Tuple[str, str]:
        return entity_sort_key(ec)

    def _side_sort_key(self, side: str) -> Tuple[int, str]:
        return side_sort_key(side)

    def _collect_tree_rows(
        self, *, include_hidden: bool
    ) -> List[Tuple[int, List[str], str]]:
        columns = self.tree.columnCount()
        rows: List[Tuple[int, List[str], str]] = []
        root = self.tree.invisibleRootItem()

        def visit(parent: QTreeWidgetItem, level: int) -> None:
            for idx in range(parent.childCount()):
                child = parent.child(idx)
                if not include_hidden and child.isHidden():
                    continue
                texts = [child.text(col) for col in range(columns)]
                data = child.data(0, Qt.ItemDataRole.UserRole)
                if isinstance(data, str):
                    kind = "side"
                elif isinstance(data, tuple) and data:
                    if data[0] == "unit":
                        kind = "unit"
                    elif data[0] == "entity":
                        kind = "entity"
                    else:
                        kind = "node"
                else:
                    kind = "group"
                rows.append((level, texts, kind))
                visit(child, level + 1)

        visit(root, 0)
        return rows

    def _write_preview_excel(
        self, path: str, rows: List[Tuple[int, List[str], str]]
    ) -> None:
        from openpyxl import Workbook
        from openpyxl.styles import Alignment, Font

        wb = Workbook()
        ws = wb.active
        ws.title = "Preview"
        headers = ["Hierarchy", "2525C"]
        ws.append(headers)
        header_font = Font(bold=True)
        for col_index, header in enumerate(headers, start=1):
            cell = ws.cell(row=1, column=col_index)
            cell.font = header_font
            cell.alignment = Alignment(horizontal="left", vertical="center")
        row_count = len(rows)
        for idx, (level, texts, kind) in enumerate(rows):
            row_index = idx + 2
            label = texts[0] if texts else ""
            code = texts[1] if len(texts) > 1 else ""
            space_prefix = " " * max(level * 2, 0)
            display_label = f"{space_prefix}{label}" if label else ""
            cell_label = ws.cell(row=row_index, column=1, value=display_label)
            cell_code = ws.cell(row=row_index, column=2, value=code or None)
            indent = min(level, 15)
            cell_label.alignment = Alignment(indent=indent, vertical="center")
            cell_code.alignment = Alignment(vertical="center")
            next_level = rows[idx + 1][0] if idx + 1 < row_count else None
            has_children = next_level is not None and next_level > level
            font = None
            if kind == "side":
                font = Font(bold=True)
            elif kind == "unit" and has_children:
                font = Font(bold=True)
            elif kind == "entity":
                font = Font(italic=True)
            elif kind == "group":
                font = Font(italic=True)
            if font is not None:
                cell_label.font = font
            if level > 0:
                ws.row_dimensions[row_index].outlineLevel = min(level, 7)
        ws.column_dimensions["A"].width = 64
        ws.column_dimensions["B"].width = 18
        ws.freeze_panes = "A2"
        ws.sheet_view.showOutlineSymbols = True
        ws.sheet_properties.outlinePr.summaryBelow = False
        ws.sheet_properties.outlinePr.summaryRight = False
        ws.column_dimensions.group("B", "B", outline_level=1, hidden=False)
        wb.save(path)


class ObsUnitSelectionDialog(QDialog):

    def __init__(self, parent: Optional[QWidget], model: ObsModel):
        super().__init__(parent)
        self._model = model
        self._selected_roots: Set[ET._Element] = set()
        self.setWindowTitle("Select Units to Import")
        self.resize(680, 540)
        layout = QVBoxLayout(self)
        layout.addWidget(
            QLabel("Choose the root units to merge into the current model.")
        )
        self.tree = QTreeWidget()
        self.tree.setAlternatingRowColors(True)
        self.tree.setColumnCount(3)
        self.tree.setHeaderLabels(["Unit", "LvcId", "2525C"])
        self.tree.setRootIsDecorated(True)
        self.tree.setUniformRowHeights(True)
        self.tree.itemChanged.connect(self._on_item_changed)
        layout.addWidget(self.tree)
        ctrl_row = QHBoxLayout()
        btn_all = QPushButton("Select All")
        btn_none = QPushButton("Select None")
        btn_expand = QPushButton("Expand All")
        btn_collapse = QPushButton("Collapse All")
        btn_all.clicked.connect(lambda: self._set_all(Qt.CheckState.Checked))
        btn_none.clicked.connect(lambda: self._set_all(Qt.CheckState.Unchecked))
        btn_expand.clicked.connect(self.tree.expandAll)
        btn_collapse.clicked.connect(self.tree.collapseAll)
        for btn in (btn_all, btn_none, btn_expand, btn_collapse):
            ctrl_row.addWidget(btn)
        ctrl_row.addStretch()
        layout.addLayout(ctrl_row)
        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(self._on_accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        self._populate_tree()
        self.tree.expandToDepth(0)

    def _populate_tree(self) -> None:
        model = self._model
        if model is None:
            return
        lvc_to_unit, parent_to_children = collect_unit_maps(model)
        self._parent_to_children = parent_to_children
        self._visited_units: Set[int] = set()
        units = list(_iter_local(model.unit_list, "Unit"))
        side_labels: Dict[str, str] = {}

        def unit_side(unit: ET._Element) -> str:
            raw = (text(jfind(unit, "j:SideSuperior")) or "").strip()
            if raw:
                side_labels.setdefault(raw.upper(), raw)
                return raw.upper()
            derived = _resolve_unit_side(unit, lvc_to_unit)
            if derived:
                side_labels.setdefault(derived.upper(), derived)
                return derived.upper()
            side_labels.setdefault("UNKNOWN", "UNKNOWN")
            return "UNKNOWN"

        side_roots: Dict[str, List[ET._Element]] = {}
        for unit in units:
            superior = (text(jfind(unit, "j:UnitSuperior")) or "").strip()
            if superior and superior in lvc_to_unit:
                continue
            key = unit_side(unit)
            side_roots.setdefault(key, []).append(unit)
        side_items: Dict[str, QTreeWidgetItem] = {}
        self.tree.blockSignals(True)
        for side_key in sorted(side_roots.keys(), key=side_sort_key):
            display = side_labels.get(side_key, side_key)
            side_item = QTreeWidgetItem([display, "", ""])
            side_item.setFlags(side_item.flags() & ~Qt.ItemFlag.ItemIsUserCheckable)
            self.tree.addTopLevelItem(side_item)
            side_items[side_key] = side_item
            roots = sorted(side_roots.get(side_key, []), key=unit_sort_key)
            for unit in roots:
                self._add_unit_item(side_item, unit)
        # Catch any units that did not appear due to missing superior references
        remaining = [u for u in units if id(u) not in self._visited_units]
        if remaining:
            side_item = side_items.get("UNKNOWN")
            if side_item is None:
                side_item = QTreeWidgetItem(["UNKNOWN / Unassigned", "", ""])
                side_item.setFlags(side_item.flags() & ~Qt.ItemFlag.ItemIsUserCheckable)
                self.tree.addTopLevelItem(side_item)
            placeholder = QTreeWidgetItem(["Detached Units", "", ""])
            placeholder.setFlags(placeholder.flags() & ~Qt.ItemFlag.ItemIsUserCheckable)
            side_item.addChild(placeholder)
            for unit in sorted(remaining, key=unit_sort_key):
                self._add_unit_item(placeholder, unit)
        self.tree.blockSignals(False)
        self._refresh_parent_states()

    def _add_unit_item(self, parent_item: QTreeWidgetItem, unit: ET._Element) -> None:
        if id(unit) in self._visited_units:
            return
        self._visited_units.add(id(unit))
        label = format_unit_label(unit)
        lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        code = (text(jfind(unit, "j:MilStd2525CCode")) or "").strip()
        item = QTreeWidgetItem([label, lvc, code])
        flags = (
            item.flags()
            | Qt.ItemFlag.ItemIsUserCheckable
            | Qt.ItemFlag.ItemIsSelectable
            | Qt.ItemFlag.ItemIsAutoTristate
        )
        item.setFlags(flags)
        item.setCheckState(0, Qt.CheckState.Checked)
        item.setData(0, Qt.ItemDataRole.UserRole, unit)
        parent_item.addChild(item)
        children = []
        if lvc:
            children = sorted(self._parent_to_children.get(lvc, []), key=unit_sort_key)
        for child in children:
            self._add_unit_item(item, child)

    def _set_all(self, state: Qt.CheckState) -> None:
        self.tree.blockSignals(True)

        def set_item(item: QTreeWidgetItem) -> None:
            if item.flags() & Qt.ItemFlag.ItemIsUserCheckable:
                item.setCheckState(0, state)
            for idx in range(item.childCount()):
                set_item(item.child(idx))

        for i in range(self.tree.topLevelItemCount()):
            set_item(self.tree.topLevelItem(i))
        self.tree.blockSignals(False)
        self._refresh_parent_states()

    def _on_item_changed(self, item: QTreeWidgetItem, column: int) -> None:
        if column != 0:
            return
        state = item.checkState(0)
        self.tree.blockSignals(True)
        for idx in range(item.childCount()):
            item.child(idx).setCheckState(0, state)
        self.tree.blockSignals(False)
        self._update_parent_state(item)

    def _update_parent_state(self, item: QTreeWidgetItem) -> None:
        parent = item.parent()
        while parent is not None:
            checked = unchecked = partial = 0
            for idx in range(parent.childCount()):
                child_state = parent.child(idx).checkState(0)
                if child_state == Qt.CheckState.Checked:
                    checked += 1
                elif child_state == Qt.CheckState.Unchecked:
                    unchecked += 1
                else:
                    partial += 1
            self.tree.blockSignals(True)
            if partial > 0 or (checked > 0 and unchecked > 0):
                parent.setCheckState(0, Qt.CheckState.PartiallyChecked)
            elif checked == parent.childCount():
                parent.setCheckState(0, Qt.CheckState.Checked)
            else:
                parent.setCheckState(0, Qt.CheckState.Unchecked)
            self.tree.blockSignals(False)
            parent = parent.parent()

    def _refresh_parent_states(self) -> None:
        def refresh(item: QTreeWidgetItem) -> Qt.CheckState:
            child_states = []
            for idx in range(item.childCount()):
                child_states.append(refresh(item.child(idx)))
            if not child_states:
                return item.checkState(0)
            if all(state == Qt.CheckState.Checked for state in child_states):
                state = Qt.CheckState.Checked
            elif all(state == Qt.CheckState.Unchecked for state in child_states):
                state = Qt.CheckState.Unchecked
            else:
                state = Qt.CheckState.PartiallyChecked
            self.tree.blockSignals(True)
            item.setCheckState(0, state)
            self.tree.blockSignals(False)
            return state

        for i in range(self.tree.topLevelItemCount()):
            refresh(self.tree.topLevelItem(i))

    def _collect_roots(self, item: QTreeWidgetItem, out: Set[ET._Element]) -> None:
        data = item.data(0, Qt.ItemDataRole.UserRole)
        state = item.checkState(0)
        parent = item.parent()
        parent_checked = (
            parent.checkState(0) if parent is not None else Qt.CheckState.Unchecked
        )
        parent_data = (
            parent.data(0, Qt.ItemDataRole.UserRole) if parent is not None else None
        )
        if isinstance(data, ET._Element) and state == Qt.CheckState.Checked:
            if (
                parent is None
                or parent_data is None
                or parent_checked != Qt.CheckState.Checked
            ):
                out.add(data)
                return
        for idx in range(item.childCount()):
            self._collect_roots(item.child(idx), out)

    def _on_accept(self) -> None:
        selected: Set[ET._Element] = set()
        for i in range(self.tree.topLevelItemCount()):
            self._collect_roots(self.tree.topLevelItem(i), selected)
        if not selected:
            QMessageBox.warning(
                self, "Import Units", "Select at least one unit to import."
            )
            return
        self._selected_roots = selected
        super().accept()

    def selected_root_units(self) -> Set[ET._Element]:
        return set(self._selected_roots)


def merge_obs_units(
    target_model: ObsModel,
    source_model: ObsModel,
    root_units: Iterable[ET._Element],
    *,
    override_side: Optional[str] = None,
    fallback_side: Optional[str] = None,
) -> Dict[str, Any]:

    if target_model is None:
        raise ValueError("Target model is not initialized")
    if source_model is None:
        raise ValueError("Source model is not initialized")
    normalized_override = (override_side or "").strip() or None
    normalized_fallback = (fallback_side or "").strip() or None
    stats: Dict[str, Any] = {
        "units_added": 0,
        "entities_added": 0,
        "unit_lvc_conflicts": 0,
        "entity_lvc_conflicts": 0,
        "unit_superiors_cleared": 0,
        "unit_superiors_updated": 0,
        "sides_forced": 0,
        "sides_filled": 0,
        "ecc_added": 0,
        "ecc_skipped": 0,
        "ucl_added": 0,
        "ucl_skipped": 0,
        "sides_added": 0,
        "unit_ids_assigned": 0,
        "unit_timestamps_assigned": 0,
        "unit_sides_assigned": 0,
        "entities_skipped_orphaned": 0,
        "new_units": [],
    }
    root_list: List[ET._Element] = []
    seen_roots: Set[int] = set()
    for unit in root_units:
        if unit is None:
            continue
        key = id(unit)
        if key in seen_roots:
            continue
        seen_roots.add(key)
        root_list.append(unit)
    if not root_list:
        return stats

    # Merge class lists first so that references remain valid.
    def _merge_classes(tag: str, key_fn) -> Tuple[int, int]:
        src_parent = jfind(source_model.classdata, f"j:{tag}")
        if src_parent is None:
            return 0, 0
        tgt_parent = jfind(target_model.classdata, f"j:{tag}")
        if tgt_parent is None:
            tgt_parent = ET.SubElement(target_model.classdata, jtag(tag))
        existing_keys: Set[str] = set()
        for elem in list(tgt_parent):
            key = key_fn(elem)
            if key:
                existing_keys.add(key)
        added = skipped = 0
        for elem in list(src_parent):
            key = key_fn(elem)
            if not key:
                continue
            if key in existing_keys:
                skipped += 1
                continue
            tgt_parent.append(clone_element(elem))
            existing_keys.add(key)
            added += 1
        return added, skipped

    def _ecc_key(elem: ET._Element) -> Optional[str]:
        return (text(jfind(elem, "j:Name")) or "").strip().upper() or None

    def _ucl_key(elem: ET._Element) -> Optional[str]:
        return (text(jfind(elem, "j:AggregateName")) or "").strip().upper() or None

    ecc_added, ecc_skipped = _merge_classes("EntityCompositionClassList", _ecc_key)
    ucl_added, ucl_skipped = _merge_classes("UnitClassList", _ucl_key)
    stats["ecc_added"] = ecc_added
    stats["ecc_skipped"] = ecc_skipped
    stats["ucl_added"] = ucl_added
    stats["ucl_skipped"] = ucl_skipped
    used_lvc_ids: Set[str] = set()
    used_xml_ids: Set[str] = set()
    existing_unit_lvc: Dict[str, ET._Element] = {}
    for unit in _iter_local(target_model.unit_list, "Unit"):
        lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        if lvc:
            used_lvc_ids.add(lvc)
            existing_unit_lvc[lvc] = unit
        unit_id = unit.get("id")
        if unit_id:
            used_xml_ids.add(unit_id)
    for entity in _iter_local(target_model.entcomp_list, "EntityComposition"):
        lvc = (text(jfind(entity, "j:LvcId")) or "").strip()
        if lvc:
            used_lvc_ids.add(lvc)
        entity_id = entity.get("id")
        if entity_id:
            used_xml_ids.add(entity_id)
    lvc_to_unit_src, parent_to_children_src = collect_unit_maps(source_model)
    ordered_units: List[ET._Element] = []
    visited_units: Set[int] = set()

    def visit(unit: ET._Element) -> None:
        key = id(unit)
        if key in visited_units:
            return
        visited_units.add(key)
        ordered_units.append(unit)
        lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        children = []
        if lvc:
            children = parent_to_children_src.get(lvc, [])
        for child in sorted(children, key=unit_sort_key):
            visit(child)

    for unit in sorted(root_list, key=unit_sort_key):
        visit(unit)
    selected_unit_lvc: Set[str] = set()
    for unit in ordered_units:
        lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        if lvc:
            selected_unit_lvc.add(lvc)
    entities_to_copy: List[ET._Element] = []
    if selected_unit_lvc:
        for entity in _iter_local(source_model.entcomp_list, "EntityComposition"):
            sup = (text(jfind(entity, "j:UnitSuperior")) or "").strip()
            if sup and sup in selected_unit_lvc:
                entities_to_copy.append(entity)
    unit_lvc_map: Dict[str, str] = {}
    new_unit_elements: List[ET._Element] = []
    imported_sides: Set[str] = set()
    override_upper = (
        normalized_override.strip().upper() if normalized_override else None
    )
    fallback_upper = (
        normalized_fallback.strip().upper() if normalized_fallback else None
    )
    for unit in ordered_units:
        new_unit = clone_element(unit)
        orig_lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        lvc_elem = jfind(new_unit, "j:LvcId")
        new_lvc = orig_lvc
        if not new_lvc or new_lvc in used_lvc_ids:
            if orig_lvc and orig_lvc in used_lvc_ids:
                stats["unit_lvc_conflicts"] += 1
            new_lvc = _gen_unique_lvcid("U", used_lvc_ids)
            if lvc_elem is None:
                lvc_elem = ET.SubElement(new_unit, jtag("LvcId"))
            lvc_elem.text = new_lvc
        else:
            used_lvc_ids.add(new_lvc)
        if orig_lvc:
            unit_lvc_map[orig_lvc] = new_lvc
        else:
            unit_lvc_map[new_lvc] = new_lvc
        unit_id = new_unit.get("id")
        if not _is_valid_unit_xml_id(unit_id) or unit_id in used_xml_ids:
            unit_id = _gen_unit_xml_id(used_xml_ids)
            new_unit.set("id", unit_id)
        used_xml_ids.add(unit_id)
        stamp = new_unit.get("dateTimeStamp")
        if not _is_valid_timestamp(stamp):
            new_unit.set("dateTimeStamp", _now_iso_seconds_no_tz())
        sup_el = jfind(new_unit, "j:UnitSuperior")
        sup_val = (
            (sup_el.text or "").strip() if sup_el is not None and sup_el.text else ""
        )
        if sup_val:
            if sup_val in unit_lvc_map:
                new_sup = unit_lvc_map[sup_val]
                if new_sup != sup_val:
                    stats["unit_superiors_updated"] += 1
                if sup_el is None:
                    sup_el = ET.SubElement(new_unit, jtag("UnitSuperior"))
                sup_el.text = new_sup
            elif sup_val in existing_unit_lvc:
                new_sup = sup_val
                if sup_el is None:
                    sup_el = ET.SubElement(new_unit, jtag("UnitSuperior"))
                sup_el.text = new_sup
            else:
                stats["unit_superiors_cleared"] += 1
                if sup_el is not None:
                    sup_el.text = ""
        # Apply side policies
        side_el = jfind(new_unit, "j:SideSuperior")
        current_side = (
            (side_el.text or "").strip() if side_el is not None and side_el.text else ""
        )
        assigned_side = current_side
        if normalized_override:
            assigned_side = normalized_override
            if side_el is None:
                side_el = ET.SubElement(new_unit, jtag("SideSuperior"))
            if side_el.text != normalized_override:
                side_el.text = normalized_override
                stats["sides_forced"] += 1
        elif not current_side and normalized_fallback:
            assigned_side = normalized_fallback
            if side_el is None:
                side_el = ET.SubElement(new_unit, jtag("SideSuperior"))
            side_el.text = normalized_fallback
            stats["sides_filled"] += 1
        if assigned_side:
            imported_sides.add(assigned_side)
        target_model.unit_list.append(new_unit)
        stats["units_added"] += 1
        new_unit_elements.append(new_unit)
        existing_unit_lvc[new_lvc] = new_unit
    entity_added = 0
    entity_lvc_map: Dict[str, str] = {}
    for entity in entities_to_copy:
        new_entity = clone_element(entity)
        orig_lvc = (text(jfind(entity, "j:LvcId")) or "").strip()
        lvc_elem = jfind(new_entity, "j:LvcId")
        new_lvc = orig_lvc
        if not new_lvc or new_lvc in used_lvc_ids:
            if orig_lvc and orig_lvc in used_lvc_ids:
                stats["entity_lvc_conflicts"] += 1
            new_lvc = _gen_unique_lvcid("E", used_lvc_ids)
            if lvc_elem is None:
                lvc_elem = ET.SubElement(new_entity, jtag("LvcId"))
            lvc_elem.text = new_lvc
        else:
            used_lvc_ids.add(new_lvc)
        if orig_lvc:
            entity_lvc_map[orig_lvc] = new_lvc
        entity_id = new_entity.get("id")
        if not entity_id or entity_id in used_xml_ids:
            entity_id = _gen_unit_xml_id(used_xml_ids)
            new_entity.set("id", entity_id)
        used_xml_ids.add(entity_id)
        sup_el = jfind(new_entity, "j:UnitSuperior")
        sup_val = (
            (sup_el.text or "").strip() if sup_el is not None and sup_el.text else ""
        )
        if sup_val:
            if sup_val in unit_lvc_map:
                new_sup = unit_lvc_map[sup_val]
            elif sup_val in existing_unit_lvc:
                new_sup = sup_val
            else:
                new_sup = ""
            if not new_sup:
                stats["entities_skipped_orphaned"] += 1
                continue
            if sup_el is None:
                sup_el = ET.SubElement(new_entity, jtag("UnitSuperior"))
            sup_el.text = new_sup
        target_model.entcomp_list.append(new_entity)
        entity_added += 1
    stats["entities_added"] = entity_added
    if imported_sides:
        stats["sides_added"] = ensure_side_entries(target_model, imported_sides)
    if new_unit_elements:
        ids_assigned, stamps_assigned, sides_assigned = ensure_unit_metadata(
            target_model,
            normalized_override or normalized_fallback,
            set(new_unit_elements),
        )
        stats["unit_ids_assigned"] = ids_assigned
        stats["unit_timestamps_assigned"] = stamps_assigned
        stats["unit_sides_assigned"] = sides_assigned
    stats["new_units"] = new_unit_elements
    return stats


class ObsMoveUnitDialog(QDialog):

    def __init__(
        self,
        parent: Optional[QWidget],
        model: ObsModel,
        *,
        blocked_units: Optional[Set[ET._Element]] = None,
        allow_side_selection: bool = True,
    ):
        super().__init__(parent)
        self._model = model
        self._allow_side_selection = allow_side_selection
        self._result: Optional[Tuple[str, Any]] = None
        self._blocked: Set[int] = {id(unit) for unit in (blocked_units or set())}
        self.setWindowTitle("Select New Parent")
        self.resize(640, 520)
        layout = QVBoxLayout(self)
        layout.addWidget(QLabel("Choose the destination for the selected item."))
        self.tree = QTreeWidget()
        self.tree.setAlternatingRowColors(True)
        self.tree.setColumnCount(3)
        self.tree.setHeaderLabels(["Unit / Side", "LvcId", "2525C"])
        self.tree.setSelectionMode(QTreeWidget.SelectionMode.SingleSelection)
        layout.addWidget(self.tree)
        self._status = QLabel("")
        layout.addWidget(self._status)
        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(self._on_accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        if model is not None:
            self._build_tree(blocked_units or set())
            self.tree.expandToDepth(1)
            self.tree.currentItemChanged.connect(self._on_current_item_changed)

    def _collect_blocked_descendants(self, blocked_units: Set[ET._Element]) -> None:
        if self._model is None or not blocked_units:
            return
        _, parent_to_children = collect_unit_maps(self._model)
        for unit in blocked_units:
            for desc in _gather_unit_descendants(
                unit, parent_to_children, include_root=True
            ):
                self._blocked.add(id(desc))

    def _build_tree(self, blocked_units: Set[ET._Element]) -> None:
        self.tree.clear()
        self._collect_blocked_descendants(blocked_units)
        model = self._model
        if model is None:
            return
        id_to_unit, parent_to_children = collect_unit_maps(model)
        side_labels: Dict[str, str] = {}

        def unit_side(unit: ET._Element) -> str:
            raw = (text(jfind(unit, "j:SideSuperior")) or "").strip()
            if raw:
                side_labels.setdefault(raw.upper(), raw)
                return raw.upper()
            derived = _resolve_unit_side(unit, id_to_unit)
            if derived:
                side_labels.setdefault(derived.upper(), derived)
                return derived.upper()
            side_labels.setdefault("UNKNOWN", "UNKNOWN")
            return "UNKNOWN"

        roots_by_side: Dict[str, List[ET._Element]] = {}
        for unit in list(model.unit_list):
            lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
            superior = (text(jfind(unit, "j:UnitSuperior")) or "").strip()
            if superior and superior in id_to_unit:
                continue
            key = unit_side(unit)
            roots_by_side.setdefault(key, []).append(unit)
        if not roots_by_side:
            roots_by_side["UNKNOWN"] = []
            side_labels.setdefault("UNKNOWN", "UNKNOWN")
        for side_key in sorted(roots_by_side.keys(), key=side_sort_key):
            display = side_labels.get(side_key, side_key)
            shown = display
            if side_key == "UNKNOWN" and display.upper() == "UNKNOWN":
                shown = "UNKNOWN / Unassigned"
            side_item = QTreeWidgetItem([shown, "", ""])
            side_item.setData(0, Qt.ItemDataRole.UserRole, ("side", side_key, display))
            flags = side_item.flags() | Qt.ItemFlag.ItemIsEnabled
            if self._allow_side_selection:
                flags |= Qt.ItemFlag.ItemIsSelectable
            else:
                flags &= ~Qt.ItemFlag.ItemIsSelectable
            side_item.setFlags(flags)
            self.tree.addTopLevelItem(side_item)
            for unit in sorted(roots_by_side.get(side_key, []), key=unit_sort_key):
                self._add_unit_item(side_item, unit, parent_to_children)

    def _add_unit_item(
        self,
        parent_item: QTreeWidgetItem,
        unit: ET._Element,
        parent_to_children: Dict[str, List[ET._Element]],
    ) -> None:
        label = format_unit_label(unit)
        lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
        code = (text(jfind(unit, "j:MilStd2525CCode")) or "").strip()
        item = QTreeWidgetItem([label, lvc, code])
        item.setData(0, Qt.ItemDataRole.UserRole, ("unit", unit))
        flags = item.flags() | Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable
        if id(unit) in self._blocked:
            flags &= ~Qt.ItemFlag.ItemIsEnabled
            flags &= ~Qt.ItemFlag.ItemIsSelectable
        item.setFlags(flags)
        parent_item.addChild(item)
        unit_lvc = lvc
        children = parent_to_children.get(unit_lvc, []) if unit_lvc else []
        for child in sorted(children, key=unit_sort_key):
            self._add_unit_item(item, child, parent_to_children)

    def _on_current_item_changed(
        self, current: Optional[QTreeWidgetItem], previous: Optional[QTreeWidgetItem]
    ) -> None:
        if current is None:
            self._status.setText("")
            return
        data = current.data(0, Qt.ItemDataRole.UserRole)
        if not isinstance(data, tuple):
            self._status.setText("")
            return
        kind = data[0]
        if kind == "unit":
            unit = data[1]
            name = (text(jfind(unit, "j:Name")) or "").strip()
            lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
            self._status.setText(f"Destination unit: {name} [{lvc}]")
        elif kind == "side":
            self._status.setText(f"Destination side: {data[2]}")
        else:
            self._status.setText("")

    def _on_accept(self) -> None:
        current = self.tree.currentItem()
        if current is None:
            QMessageBox.information(self, "Move", "Select a destination.")
            return
        data = current.data(0, Qt.ItemDataRole.UserRole)
        if not isinstance(data, tuple):
            QMessageBox.information(self, "Move", "Select a valid destination.")
            return
        kind = data[0]
        if kind == "unit":
            unit = data[1]
            if id(unit) in self._blocked:
                QMessageBox.information(
                    self, "Move", "Cannot select the original unit or its descendants."
                )
                return
            self._result = data
        elif kind == "side":
            if not self._allow_side_selection:
                QMessageBox.information(self, "Move", "Select a unit destination.")
                return
            self._result = data
        else:
            QMessageBox.information(self, "Move", "Select a valid destination.")
            return
        super().accept()

    def selected_target(self) -> Optional[Tuple[str, Any]]:
        return self._result


class GenerateTab(QWidget):

    def __init__(self, parent):
        super().__init__(parent)
        self.model: Optional[ObsModel] = None
        self._preview_dialog: Optional[ModelPreviewDialog] = None
        self._build()

    def _build(self):
        lay = QVBoxLayout(self)
        opt_box = QGroupBox("Generation Options")
        form = QFormLayout(opt_box)
        self.cmb_consol = QComboBox()
        self.cmb_consol.addItems(["None"] + CONSOLIDATION_LEVELS)
        form.addRow("Consolidate lower echelon into parent:", self.cmb_consol)
        self.btn_autofill = QPushButton("Auto-fill LvcId (unique)")
        self.btn_autofill.clicked.connect(self.on_autofill)
        self.btn_consolidate = QPushButton("Run Consolidation")
        self.btn_consolidate.clicked.connect(self.on_consolidate)
        self.btn_fix_flags = QPushButton("Fix Empty Flags")
        self.btn_fix_flags.clicked.connect(self.on_fix_flags)
        self.btn_import_obs = QPushButton("Import Units from OBS...")
        self.btn_import_obs.clicked.connect(self.on_import_obs)
        self.btn_preview = QPushButton("Preview Model")
        self.btn_preview.clicked.connect(self.on_preview)
        self.btn_save = QPushButton("Save as New JTDS OBS XML.")
        self.btn_save.clicked.connect(self.on_save)
        btn_row = QHBoxLayout()
        btn_row.addWidget(self.btn_autofill)
        btn_row.addWidget(self.btn_consolidate)
        btn_row.addWidget(self.btn_fix_flags)
        btn_row.addWidget(self.btn_import_obs)
        btn_row.addWidget(self.btn_preview)
        btn_row.addWidget(self.btn_save)
        self.log = QTextEdit()
        self.log.setReadOnly(True)
        self.log.setMinimumHeight(180)
        lay.addWidget(opt_box)
        lay.addLayout(btn_row)
        side_grp = QGroupBox("Consolidate Sides")
        self.side_checks_layout = QHBoxLayout(side_grp)
        self.side_checks: Dict[str, QCheckBox] = {}
        for label in ["BLUFOR", "OPFOR", "NEUTRAL", "CIVILIAN", "UNKNOWN"]:
            chk = QCheckBox(label)
            chk.setChecked(True)
            self.side_checks[label] = chk
            self.side_checks_layout.addWidget(chk)
        self.side_checks_layout.addStretch()
        lay.addWidget(side_grp)
        lay.addWidget(self.log)
        grp = QGroupBox("Build Class Lists")
        gl = QGridLayout(grp)
        gl.addWidget(QLabel("EntityCompositionClass master (.xlsx):"), 0, 0)
        self.ecc_edit = QLineEdit()
        btn_ecc = QPushButton("Browse...")
        btn_ecc.clicked.connect(self.on_browse_ecc)
        gl.addWidget(self.ecc_edit, 0, 1)
        gl.addWidget(btn_ecc, 0, 2)
        gl.addWidget(QLabel("UnitClass master (.xlsx):"), 1, 0)
        self.ucl_edit = QLineEdit()
        btn_ucl = QPushButton("Browse...")
        btn_ucl.clicked.connect(self.on_browse_ucl)
        gl.addWidget(self.ucl_edit, 1, 1)
        gl.addWidget(btn_ucl, 1, 2)
        self.btn_build = QPushButton("Build Classes")
        self.btn_build.clicked.connect(self.on_build_classes)
        gl.addWidget(self.btn_build, 2, 0, 1, 3)
        lay.addWidget(grp)
        self._enable(False)

    def on_browse_ecc(self):
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Open EntityCompositionClass master",
            "",
            "Excel (*.xlsx);;All Files (*)",
        )
        if path:
            self.ecc_edit.setText(path)

    def on_browse_ucl(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open UnitClass master", "", "Excel (*.xlsx);;All Files (*)"
        )
        if path:
            self.ucl_edit.setText(path)

    def on_build_classes(self):
        if not self.model:
            QMessageBox.information(self, "No model", "Load or create a model first.")
            return
        ecc_path = self.ecc_edit.text().strip() if hasattr(self, "ecc_edit") else ""
        ucl_path = self.ucl_edit.text().strip() if hasattr(self, "ucl_edit") else ""
        try:
            cnt_ecc = (
                build_entitycomposition_classlist_from_xlsx(self.model, ecc_path)
                if ecc_path
                else 0
            )
            cnt_ucl = (
                build_unitclass_list_from_xlsx(self.model, ucl_path) if ucl_path else 0
            )
        except Exception as e:
            QMessageBox.warning(self, "Build Classes", f"Failed: {e}")
            return
        self.log.append(
            f"Built EntityCompositionClassList: {cnt_ecc} items; UnitClassList: {cnt_ucl} items."
        )

    def _enable(self, ok: bool):
        for w in [
            self.btn_autofill,
            self.btn_consolidate,
            self.btn_fix_flags,
            self.btn_import_obs,
            self.btn_preview,
            self.btn_save,
            self.cmb_consol,
        ]:
            w.setEnabled(ok)
        for chk in getattr(self, "side_checks", {}).values():
            chk.setEnabled(ok)

    def _refresh_side_checks(self) -> None:
        if not getattr(self, "side_checks_layout", None):
            return
        existing = set(getattr(self, "side_checks", {}).keys())
        if not existing and self.side_checks_layout.count() == 0:
            return
        stretch_index = (
            self.side_checks_layout.count() - 1
            if self.side_checks_layout.count()
            else None
        )
        extra_sides: Set[str] = set()
        if self.model:
            for unit in list(self.model.unit_list):
                side = (text(jfind(unit, "j:SideSuperior")) or "").strip()
                if side:
                    extra_sides.add(side.upper())
        for side in sorted(extra_sides):
            if side in existing:
                continue
            chk = QCheckBox(side)
            chk.setChecked(True)
            chk.setEnabled(self.btn_autofill.isEnabled())
            self.side_checks[side] = chk
            existing.add(side)
            if stretch_index is not None and stretch_index >= 0:
                self.side_checks_layout.insertWidget(stretch_index, chk)
                stretch_index += 1
            else:
                self.side_checks_layout.addWidget(chk)
        if self.side_checks_layout.count() == len(self.side_checks):
            self.side_checks_layout.addStretch()

    def on_import_obs(self) -> None:
        if self.model is None:
            choice = QMessageBox.question(
                self,
                "No model loaded",
                "No JTDS OBS model is currently loaded. Create a new blank model to import into?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if choice != QMessageBox.StandardButton.Yes:
                return
            self.set_model(_new_blank_model())
            if self.model is None:
                return
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Import Units from OBS",
            "",
            "OBS XML or ZIP (*.xml *.zip);;All Files (*)",
        )
        if not path:
            return
        try:
            source_model = load_obs_xml(path)
        except Exception as exc:
            traceback.print_exc()
            QMessageBox.critical(
                self, "Import Units", f"Failed to load source OBS: {exc}"
            )
            return
        picker = ObsUnitSelectionDialog(self, source_model)
        if picker.exec() != QDialog.DialogCode.Accepted:
            return
        selected_units = picker.selected_root_units()
        if not selected_units:
            QMessageBox.information(
                self, "Import Units", "No units were selected to import."
            )
            return
        lvc_to_unit_src, parent_to_children_src = collect_unit_maps(source_model)
        subtree_units: List[ET._Element] = []
        visited: Set[int] = set()

        def collect(unit: ET._Element) -> None:
            key = id(unit)
            if key in visited:
                return
            visited.add(key)
            subtree_units.append(unit)
            lvc = (text(jfind(unit, "j:LvcId")) or "").strip()
            children = parent_to_children_src.get(lvc, []) if lvc else []
            for child in sorted(children, key=unit_sort_key):
                collect(child)

        for unit in selected_units:
            collect(unit)
        source_sides: Set[str] = set()
        missing_side = False
        for unit in subtree_units:
            side_val = (text(jfind(unit, "j:SideSuperior")) or "").strip()
            if side_val:
                source_sides.add(side_val)
            else:
                missing_side = True
        available_sides: Set[str] = set(source_sides)
        if self.model is not None:
            for unit in _iter_local(self.model.unit_list, "Unit"):
                side_val = (text(jfind(unit, "j:SideSuperior")) or "").strip()
                if side_val:
                    available_sides.add(side_val)
        available_sides.update(DEFAULT_SIDE_ORDER)
        choices = ["Keep source values"]
        sorted_sides = sorted(
            {s for s in available_sides if s}, key=lambda s: s.upper()
        )
        for side in sorted_sides:
            choices.append(f"Force side {side}")
        override_side: Optional[str] = None
        fallback_side: Optional[str] = None
        if choices:
            selection, ok = QInputDialog.getItem(
                self,
                "Side Assignment",
                "SideSuperior handling for imported units:",
                choices,
                0,
                False,
            )
            if not ok:
                return
            if selection.startswith("Force side "):
                override_side = selection[len("Force side ") :].strip()
        if override_side is None and missing_side and len(source_sides) == 1:
            fallback_side = next(iter(source_sides))
        try:
            stats = merge_obs_units(
                self.model,
                source_model,
                selected_units,
                override_side=override_side,
                fallback_side=fallback_side,
            )
        except Exception as exc:
            traceback.print_exc()
            QMessageBox.critical(self, "Import Units", f"Failed to merge models: {exc}")
            return
        self.set_model(self.model)
        source_name = Path(path).name
        lines = [
            f"Imported {stats['units_added']} unit(s) and {stats['entities_added']} entity composition(s) from {source_name}.",
        ]
        if override_side:
            lines.append(f" - Forced SideSuperior='{override_side}' on imported units.")
        elif fallback_side:
            lines.append(
                f" - Missing SideSuperior values defaulted to '{fallback_side}'."
            )
        elif missing_side and not fallback_side:
            lines.append(
                " - Some imported units still lack SideSuperior; review as needed."
            )
        if stats.get("unit_lvc_conflicts"):
            lines.append(
                f" - Resolved {stats['unit_lvc_conflicts']} duplicate unit LvcId value(s)."
            )
        if stats.get("entity_lvc_conflicts"):
            lines.append(
                f" - Resolved {stats['entity_lvc_conflicts']} duplicate entity composition LvcId value(s)."
            )
        if stats.get("unit_superiors_cleared"):
            lines.append(
                f" - Cleared {stats['unit_superiors_cleared']} missing UnitSuperior reference(s)."
            )
        if stats.get("entities_skipped_orphaned"):
            lines.append(
                f" - Skipped {stats['entities_skipped_orphaned']} entity composition(s) without a parent unit in scope."
            )
        if stats.get("ecc_added") or stats.get("ucl_added"):
            lines.append(
                f" - Class list merge: EntityCompositionClass +{stats['ecc_added']}, UnitClass +{stats['ucl_added']}."
            )
        if stats.get("sides_added"):
            lines.append(
                f" - Added {stats['sides_added']} side definition(s) to Scenario/SideList."
            )
        if (
            stats.get("unit_ids_assigned")
            or stats.get("unit_timestamps_assigned")
            or stats.get("unit_sides_assigned")
        ):
            lines.append(
                f" - Unit metadata normalized: ids={stats['unit_ids_assigned']}, timestamps={stats['unit_timestamps_assigned']}, sides set={stats['unit_sides_assigned']}."
            )
        self.log.append("\n".join(lines))
        QMessageBox.information(self, "Import Units", lines[0])

    def set_model(self, model: Optional[ObsModel]):
        self.model = model
        self._enable(model is not None)
        self._refresh_side_checks()

    def on_autofill(self):
        if not self.model:
            return
        count = autofill_unique_lvcids(self.model)
        self.log.append(f"Auto-filled/Fixed LvcId fields: {count}")

    def on_consolidate(self):
        if not self.model:
            return
        mode = self.cmb_consol.currentText()
        selected_sides = {
            side
            for side, chk in getattr(self, "side_checks", {}).items()
            if chk.isChecked()
        }
        if not selected_sides:
            QMessageBox.information(
                self,
                "Consolidate",
                "Select at least one side before running consolidation.",
            )
            return
        stats = consolidate_units(self.model, mode, selected_sides)
        sides_text = ", ".join(sorted(selected_sides))
        msg = f"Consolidation '{mode}' (sides: {sides_text}): removed units {stats['removed_units']}, moved ECs {stats['moved_entity_compositions']}, reparented units {stats['relinked_units']}"
        skipped = stats.get("skipped_units", 0)
        if skipped:
            msg += f", skipped {skipped} unit(s) without a surviving parent"
        self.log.append(msg)

    def on_fix_flags(self):
        if not self.model:
            return
        try:
            stats = fix_empty_flags(self.model)
        except Exception as e:
            traceback.print_exc()
            QMessageBox.warning(self, "Fix Empty Flags", f"Failed: {e}")
            return
        total = stats.get("created", 0)
        per_side = stats.get("per_side", {})
        skipped = stats.get("skipped", 0)
        parts = [f"{side}={count}" for side, count in per_side.items() if count]
        if total:
            msg = f"Fix Empty Flags: created {total} EntityCompositions"
            if parts:
                msg += f" ({', '.join(parts)})"
            if skipped:
                msg += f"; skipped {skipped} units without side mapping"
        else:
            msg = "Fix Empty Flags: no missing UnitSuperior references found"
            if skipped:
                msg += f" (skipped {skipped} units without side mapping)"
        self.log.append(msg)

    def on_preview(self):
        if not self.model:
            QMessageBox.information(self, "No model", "Load or create a model first.")
            return
        if self._preview_dialog is None:
            self._preview_dialog = ModelPreviewDialog(self)
        self._preview_dialog.set_model(self.model)
        self._preview_dialog.exec()

    def on_save(self):
        if not self.model:
            return
        out, _ = QFileDialog.getSaveFileName(
            self, "Save JTDS OBS XML", "JTDS_Scrubbed.xml", "OBS XML (*.xml)"
        )
        if not out:
            return
        try:
            save_xml(self.model, out)
        except Exception as e:
            QMessageBox.critical(self, "Save Error", str(e))
        else:
            QMessageBox.information(self, "Saved", f"Saved to: {out}")


# === DRAGON Enhanced Import Helpers ===


def _pick_col(cols, *cands):

    up = {str(c).strip().upper(): c for c in cols}
    for cand in cands:
        if isinstance(cand, (list, tuple)):
            for x in cand:
                if x and x.upper() in up:
                    return up[x.upper()]
        elif cand and cand.upper() in up:
            return up[cand.upper()]
    # loose contains
    for c in cols:
        cu = str(c).upper()
        for cand in cands:
            if isinstance(cand, str) and cand and cand.upper() in cu:
                return c
            if isinstance(cand, (list, tuple)):
                for x in cand:
                    if x and str(x).upper() in cu:
                        return c
    return None


def _norm(s):

    return str(s).strip() if s is not None else ""


def _parse_den_to_attrs(s):

    import re as _re

    if not s:
        return {}
    parts = _re.split(r"[.\s]+", str(s).strip())
    keys = ["kind", "domain", "country", "category", "subcategory", "specific", "extra"]
    out = {}
    for i, k in enumerate(keys):
        if i < len(parts) and parts[i].isdigit():
            out[k] = parts[i]
    return out


@dataclass
class DragonUnitNode:

    uid: str
    name: str
    template: str
    parent_uid: Optional[str]
    unit_class: str
    ms2525: str
    order: int
    children: List["DragonUnitNode"]

    def display_name(self) -> str:
        base = self.name or self.uid
        if self.unit_class:
            return f"{base} [{self.unit_class}]"
        return base


@dataclass
class DragonWorkbookTree:

    roots: List[DragonUnitNode]
    node_map: Dict[str, DragonUnitNode]

    def total_units(self) -> int:
        return len(self.node_map)

    def gather_subtree_uids(self, root_uids: Set[str]) -> Set[str]:
        acc: Set[str] = set()
        for uid in root_uids:
            node = self.node_map.get(uid.upper())
            if node is not None:
                _collect_dragon_uids(node, acc)
        return acc


def _collect_dragon_uids(node: DragonUnitNode, acc: Set[str]) -> None:

    key = node.uid.strip().upper()
    if not key or key in acc:
        pass
    else:
        acc.add(key)
    for child in node.children:
        _collect_dragon_uids(child, acc)


def parse_dragon_unit_hierarchy(xlsx_path: str) -> DragonWorkbookTree:

    try:
        xls = pd.ExcelFile(xlsx_path)
    except Exception as exc:
        raise ValueError(f"Failed to open DRAGON workbook: {exc}") from exc
    if "UNIT INFO" not in xls.sheet_names:
        raise ValueError("UNIT INFO sheet not found in DRAGON workbook.")
    df = xls.parse("UNIT INFO")
    df.columns = [str(c).strip() for c in df.columns]
    col_uid = _pick_col(df.columns, "UID", "UNIT UID", "ID")
    if not col_uid:
        raise ValueError("UID column not found in UNIT INFO sheet.")
    col_name = _pick_col(
        df.columns, "UNIT", "UNIT NAME", "NAME", "UNIT TITLE", "DISPLAY NAME"
    )
    col_puid = _pick_col(df.columns, "PARENT UID", "PARENT", "PARENT ID")
    col_templ = _pick_col(
        df.columns, "TEMPLATE NAME", "TEMPLATE", "SHEET", "STRUCTURE SHEET"
    )
    col_uclass = _pick_col(df.columns, "UNIT CLASS", "AGGREGATE NAME", "CLASS")
    col_2525 = _pick_col(df.columns, "2525C", "MILSTD2525C", "MILSTD 2525C")
    nodes: Dict[str, DragonUnitNode] = {}
    order_keys: List[str] = []
    for idx, row in df.iterrows():
        uid_raw = _norm(row.get(col_uid)) if col_uid else ""
        if not uid_raw:
            continue
        uid = uid_raw.strip()
        key = uid.upper()
        if key in nodes:
            continue
        name = _norm(row.get(col_name)) if col_name else ""
        template = _norm(row.get(col_templ)) if col_templ else ""
        parent_uid = _norm(row.get(col_puid)) if col_puid else ""
        unit_class = _norm(row.get(col_uclass)) if col_uclass else ""
        ms2525 = _norm(row.get(col_2525)) if col_2525 else ""
        node = DragonUnitNode(
            uid=uid,
            name=name or uid,
            template=template,
            parent_uid=parent_uid or None,
            unit_class=unit_class,
            ms2525=ms2525,
            order=idx,
            children=[],
        )
        nodes[key] = node
        order_keys.append(key)
    if not nodes:
        raise ValueError("No units with UID values were found in UNIT INFO sheet.")
    roots: List[DragonUnitNode] = []
    for key in order_keys:
        node = nodes[key]
        p_key = node.parent_uid.strip().upper() if node.parent_uid else ""
        if p_key and p_key in nodes:
            nodes[p_key].children.append(node)
        else:
            roots.append(node)
    return DragonWorkbookTree(roots=roots, node_map=nodes)


def di_import_dragon_enhanced(
    model: "ObsModel" | None,
    xlsx_path: str,
    unitlist_map: Optional[Dict[str, Dict[str, str]]] = None,
    default_side: Optional[str] = None,
    selected_uids: Optional[Set[str]] = None,
    *,
    progress_cb: Optional[Callable[[str, float], None]] = None,
    cancel_cb: Optional[Callable[[], bool]] = None,
) -> Tuple[ObsModel, int, int]:

    if cli_import_dragon_enhanced is None:
        raise RuntimeError("dragon_importer_new.import_dragon_enhanced is unavailable")
    if model is None:
        model = _new_blank_model()

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

    before_units = set(_iter_local(model.unit_list, "Unit"))
    _emit("Starting DRAGON workbook import...", 0.1)

    def _import_progress(message: str, inner_fraction: float) -> None:
        scaled = 0.2 + max(0.0, min(inner_fraction, 1.0)) * 0.6
        _emit(message, min(scaled, 0.85))
        _check_cancel()

    cli_import_dragon_enhanced(
        model,
        xlsx_path,
        allowed_uids=selected_uids,
        progress_cb=_import_progress,
        cancel_cb=cancel_cb,
    )
    _emit("Normalizing imported data...", 0.87)
    if cli_normalize_to_jtds_schema is not None:
        _check_cancel()
        cli_normalize_to_jtds_schema(model)
    _emit("Auto-filling LvcId fields...", 0.9)
    autofill_unique_lvcids(model)
    if unitlist_map:
        _emit("Applying reference UnitDisEnumeration map...", 0.94)
        for unit in _iter_local(model.unit_list, "Unit"):
            _check_cancel()
            code = (text(jfind(unit, "j:MilStd2525CCode")) or "").strip()
            if not code:
                continue
            attrs = unitlist_map.get(code) or unitlist_map.get(code.upper())
            if not attrs:
                continue
            ude = jfind(unit, "j:UnitDisEnumeration")
            if ude is None:
                ude = ET.SubElement(unit, jtag("UnitDisEnumeration"))
            for k, v in attrs.items():
                if ude.get(k) in (None, "") and v not in (None, ""):
                    ude.set(k, str(v))
    after_units = set(_iter_local(model.unit_list, "Unit"))
    new_units = after_units - before_units
    _emit("Finalizing import metadata...", 0.97)
    _check_cancel()
    unit_meta = ensure_unit_metadata(model, default_side, new_units)
    units = len(list(model.unit_list))
    ecs = len(list(model.entcomp_list))
    try:
        existing = getattr(model, "_dragon_counts", {})
        existing.update({"units": units, "ecs": ecs, "unit_meta": unit_meta})
        setattr(model, "_dragon_counts", existing)
    except Exception:
        pass
    _emit("Import complete", 1.0)
    return model, units, ecs


class DragonUnitSelectionDialog(QDialog):

    def __init__(
        self, parent, tree: DragonWorkbookTree, preselected: Optional[Set[str]] = None
    ):
        super().__init__(parent)
        self.setWindowTitle("Select DRAGON Units")
        self.resize(540, 520)
        self._tree = tree
        self._selected_root_uids: Set[str] = set()
        layout = QVBoxLayout(self)
        self.tree_widget = QTreeWidget()
        self.tree_widget.setColumnCount(3)
        self.tree_widget.setHeaderLabels(["Unit", "UID", "Template"])
        self.tree_widget.setAlternatingRowColors(True)
        layout.addWidget(self.tree_widget)
        prechecked = {uid.upper() for uid in (preselected or tree.node_map.keys())}
        self._populate_tree(tree.roots, prechecked)
        self.tree_widget.expandToDepth(1)
        self.tree_widget.itemChanged.connect(self._on_item_changed)
        ctrl_row = QHBoxLayout()
        btn_all = QPushButton("Select All")
        btn_none = QPushButton("Clear")
        btn_expand = QPushButton("Expand")
        btn_collapse = QPushButton("Collapse")
        btn_all.clicked.connect(lambda: self._set_all(Qt.CheckState.Checked))
        btn_none.clicked.connect(lambda: self._set_all(Qt.CheckState.Unchecked))
        btn_expand.clicked.connect(self.tree_widget.expandAll)
        btn_collapse.clicked.connect(self.tree_widget.collapseAll)
        for btn in (btn_all, btn_none, btn_expand, btn_collapse):
            ctrl_row.addWidget(btn)
        ctrl_row.addStretch()
        layout.addLayout(ctrl_row)
        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(self._on_accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

    def _populate_tree(self, nodes: List[DragonUnitNode], prechecked: Set[str]) -> None:
        self.tree_widget.blockSignals(True)

        def add_node(
            node: DragonUnitNode, parent_item: Optional[QTreeWidgetItem]
        ) -> None:
            texts = [node.display_name(), node.uid, node.template or ""]
            item = QTreeWidgetItem(texts)
            item.setData(0, Qt.ItemDataRole.UserRole, node.uid.strip().upper())
            state = (
                Qt.CheckState.Checked
                if node.uid.strip().upper() in prechecked
                else Qt.CheckState.Unchecked
            )
            item.setCheckState(0, state)
            if parent_item is not None:
                parent_item.addChild(item)
            else:
                self.tree_widget.addTopLevelItem(item)
            for child in node.children:
                add_node(child, item)

        for node in nodes:
            add_node(node, None)
        self.tree_widget.blockSignals(False)
        self._refresh_parent_states()

    def _refresh_parent_states(self) -> None:
        def refresh(item: QTreeWidgetItem) -> Qt.CheckState:
            child_states = []
            for idx in range(item.childCount()):
                child_states.append(refresh(item.child(idx)))
            if not child_states:
                return item.checkState(0)
            if all(state == Qt.CheckState.Checked for state in child_states):
                state = Qt.CheckState.Checked
            elif all(state == Qt.CheckState.Unchecked for state in child_states):
                state = Qt.CheckState.Unchecked
            else:
                state = Qt.CheckState.PartiallyChecked
            self.tree_widget.blockSignals(True)
            item.setCheckState(0, state)
            self.tree_widget.blockSignals(False)
            return state

        for i in range(self.tree_widget.topLevelItemCount()):
            refresh(self.tree_widget.topLevelItem(i))

    def _set_all(self, state: Qt.CheckState) -> None:
        self.tree_widget.blockSignals(True)

        def set_item(item: QTreeWidgetItem) -> None:
            item.setCheckState(0, state)
            for idx in range(item.childCount()):
                set_item(item.child(idx))

        for i in range(self.tree_widget.topLevelItemCount()):
            set_item(self.tree_widget.topLevelItem(i))
        self.tree_widget.blockSignals(False)
        self._refresh_parent_states()

    def _on_item_changed(self, item: QTreeWidgetItem, column: int) -> None:
        if column != 0:
            return
        state = item.checkState(0)
        self.tree_widget.blockSignals(True)
        for idx in range(item.childCount()):
            item.child(idx).setCheckState(0, state)
        self.tree_widget.blockSignals(False)
        self._update_parent_state(item)

    def _update_parent_state(self, item: QTreeWidgetItem) -> None:
        parent = item.parent()
        while parent is not None:
            checked = 0
            unchecked = 0
            partial = 0
            for idx in range(parent.childCount()):
                ch_state = parent.child(idx).checkState(0)
                if ch_state == Qt.CheckState.Checked:
                    checked += 1
                elif ch_state == Qt.CheckState.Unchecked:
                    unchecked += 1
                else:
                    partial += 1
            self.tree_widget.blockSignals(True)
            if partial > 0 or (checked > 0 and unchecked > 0):
                parent.setCheckState(0, Qt.CheckState.PartiallyChecked)
            elif checked == parent.childCount():
                parent.setCheckState(0, Qt.CheckState.Checked)
            else:
                parent.setCheckState(0, Qt.CheckState.Unchecked)
            self.tree_widget.blockSignals(False)
            parent = parent.parent()

    def _collect_roots(self, item: QTreeWidgetItem, out: Set[str]) -> None:
        state = item.checkState(0)
        uid = item.data(0, Qt.ItemDataRole.UserRole)
        if state == Qt.CheckState.Checked and uid:
            out.add(str(uid))
            return
        if state == Qt.CheckState.Unchecked:
            return
        for idx in range(item.childCount()):
            self._collect_roots(item.child(idx), out)

    def _on_accept(self) -> None:
        roots: Set[str] = set()
        for i in range(self.tree_widget.topLevelItemCount()):
            self._collect_roots(self.tree_widget.topLevelItem(i), roots)
        if not roots:
            QMessageBox.warning(
                self, "Select DRAGON Units", "Select at least one unit to import."
            )
            return
        self._selected_root_uids = roots
        super().accept()

    def selected_root_uids(self) -> Set[str]:
        return set(self._selected_root_uids)


class DragonImportWorker(QObject):

    progress = pyqtSignal(str, float)
    finished = pyqtSignal(object, int, int, bool)
    failed = pyqtSignal(str)
    cancelled = pyqtSignal()

    def __init__(
        self,
        model: ObsModel,
        dragon_path: str,
        ref_xml_path: Optional[str],
        selected_side: str,
        selected_uids: Optional[Set[str]],
    ):
        super().__init__()
        self._model = model
        self._dragon_path = dragon_path
        self._ref_xml_path = ref_xml_path
        self._selected_side = selected_side
        self._selected_uids = selected_uids
        self._cancel_requested = False

    def request_cancel(self) -> None:
        self._cancel_requested = True

    def _is_cancelled(self) -> bool:
        return self._cancel_requested

    @pyqtSlot()
    def run(self) -> None:
        try:
            self.progress.emit("Preparing import...", 0.0)
            ref_map: Optional[Dict[str, Dict[str, str]]] = None
            ref_applied = False
            if self._ref_xml_path:
                self.progress.emit("Loading reference unitlist.xml ...", 0.05)
                ref_map = load_unitlist_map(self._ref_xml_path)
                ref_applied = True

            def progress_cb(message: str, fraction: float) -> None:
                self.progress.emit(message, fraction)

            def cancel_cb() -> bool:
                return self._is_cancelled()

            base_model = self._model if self._model is not None else _new_blank_model()
            working_model = clone_obs_model(base_model)

            model, units, ecs = di_import_dragon_enhanced(
                working_model,
                self._dragon_path,
                ref_map,
                self._selected_side,
                self._selected_uids,
                progress_cb=progress_cb,
                cancel_cb=cancel_cb,
            )
            self.finished.emit(model, units, ecs, ref_applied)
        except DragonImportCancelled:
            self.cancelled.emit()
        except Exception as exc:
            traceback.print_exc()
            self.failed.emit(str(exc))


class ImportDragonTab(QWidget):

    modelImported = pyqtSignal(object)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.model: Optional[ObsModel] = None
        self._dragon_tree: Optional[DragonWorkbookTree] = None
        self._dragon_tree_path: Optional[str] = None
        self._dragon_selected_roots: Optional[Set[str]] = None
        self._import_thread: Optional[QThread] = None
        self._import_worker: Optional[DragonImportWorker] = None
        self._pending_selected_uids: Optional[Set[str]] = None
        self._pending_side: Optional[str] = None
        self._build_ui()

    def _build_ui(self):
        outer = QVBoxLayout(self)
        row1 = QHBoxLayout()
        self.path_edit = QLineEdit()
        self.path_edit.setPlaceholderText("Select DRAGON workbook (.xlsx)...")
        self.path_edit.textChanged.connect(self._on_dragon_path_changed)
        btn1 = QPushButton("Browse...")
        btn1.clicked.connect(self.on_browse_dragon)
        row1.addWidget(self.path_edit)
        row1.addWidget(btn1)
        outer.addLayout(row1)
        row2 = QHBoxLayout()
        self.ref_edit = QLineEdit()
        self.ref_edit.setPlaceholderText("Select reference unitlist.xml (optional)")
        btn2 = QPushButton("Browse XML...")
        btn2.clicked.connect(self.on_browse_refxml)
        row2.addWidget(self.ref_edit)
        row2.addWidget(btn2)
        outer.addLayout(row2)
        self.log = QTextEdit()
        self.log.setReadOnly(True)
        self.log.setMinimumHeight(220)
        outer.addWidget(self.log)
        progress_row = QHBoxLayout()
        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.progress_bar.setFormat("Idle")
        progress_row.addWidget(self.progress_bar, 1)
        self.btn_cancel_import = QPushButton("Cancel Import")
        self.btn_cancel_import.setEnabled(False)
        self.btn_cancel_import.clicked.connect(self._on_cancel_import)
        progress_row.addWidget(self.btn_cancel_import)
        outer.addLayout(progress_row)
        side_row = QHBoxLayout()
        side_row.addWidget(QLabel("Imported Side:"))
        self.side_group = QButtonGroup(self)
        self.side_buttons: Dict[str, QRadioButton] = {}
        for label in ("BLUFOR", "NEUTRAL", "OPFOR"):
            rb = QRadioButton(label)
            self.side_group.addButton(rb)
            self.side_buttons[label] = rb
            side_row.addWidget(rb)
            if label == "BLUFOR":
                rb.setChecked(True)
        side_row.addStretch()
        outer.addLayout(side_row)
        select_row = QHBoxLayout()
        self.btn_select_units = QPushButton("Select Units...")
        self.btn_select_units.setEnabled(False)
        self.btn_select_units.clicked.connect(self.on_select_units)
        select_row.addWidget(self.btn_select_units)
        self.selection_label = QLabel("Units: ALL")
        select_row.addWidget(self.selection_label)
        select_row.addStretch()
        outer.addLayout(select_row)
        grp = QGroupBox("Build Class Lists")
        gl = QGridLayout(grp)
        gl.addWidget(QLabel("EntityCompositionClass master (.xlsx):"), 0, 0)
        self.ecc_edit = QLineEdit()
        btn_ecc = QPushButton("Browse...")
        btn_ecc.clicked.connect(self.on_browse_ecc)
        gl.addWidget(self.ecc_edit, 0, 1)
        gl.addWidget(btn_ecc, 0, 2)
        gl.addWidget(QLabel("UnitClass master (.xlsx):"), 1, 0)
        self.ucl_edit = QLineEdit()
        btn_ucl = QPushButton("Browse...")
        btn_ucl.clicked.connect(self.on_browse_ucl)
        gl.addWidget(self.ucl_edit, 1, 1)
        gl.addWidget(btn_ucl, 1, 2)
        self.btn_build_classes = QPushButton("Build Classes")
        self.btn_build_classes.clicked.connect(self.on_build_classes)
        gl.addWidget(self.btn_build_classes, 2, 0, 1, 3)
        self.btn_append_ucl = QPushButton("Append DRAGON Unit Classes to Master")
        self.btn_append_ucl.clicked.connect(self.on_append_unitclasses)
        self.btn_append_ucl.setEnabled(cli_append_unitclasses_to_master is not None)
        gl.addWidget(self.btn_append_ucl, 3, 0, 1, 3)
        outer.addWidget(grp)
        self.btn_import = QPushButton("Import into Current Model (or New)")
        self.btn_import.clicked.connect(self.on_import)
        outer.addWidget(self.btn_import, alignment=Qt.AlignmentFlag.AlignRight)

    def _is_import_running(self) -> bool:
        return self._import_thread is not None

    def _set_import_running(self, running: bool) -> None:
        if running:
            self.progress_bar.setRange(0, 100)
            self.progress_bar.setValue(0)
            self.progress_bar.setFormat("Importing DRAGON workbook ...")
        else:
            self.progress_bar.setRange(0, 100)
            self.progress_bar.setValue(0)
            self.progress_bar.setFormat("Idle")
        enable = not running
        self.path_edit.setEnabled(enable)
        self.ref_edit.setEnabled(enable)
        self.ecc_edit.setEnabled(enable)
        self.ucl_edit.setEnabled(enable)
        self.btn_import.setEnabled(enable)
        self.btn_build_classes.setEnabled(enable)
        if hasattr(self, "btn_append_ucl") and self.btn_append_ucl is not None:
            self.btn_append_ucl.setEnabled(
                enable and cli_append_unitclasses_to_master is not None
            )
        can_select_units = enable and bool(self.path_edit.text().strip())
        self.btn_select_units.setEnabled(can_select_units)
        self.btn_cancel_import.setEnabled(running)

    def _handle_import_progress(self, message: str, fraction: float) -> None:
        pct = max(0, min(int(fraction * 100), 100))
        self.progress_bar.setValue(pct)
        if message:
            self.progress_bar.setFormat(f"{message} ({pct}%)")
            self.log.append(message)

    def _on_cancel_import(self) -> None:
        if self._import_worker:
            self._import_worker.request_cancel()
            self.btn_cancel_import.setEnabled(False)
            self.progress_bar.setFormat("Canceling import...")
            self.log.append("Cancel requested. Waiting for current import to stop...")

    def _cleanup_import_state(self) -> None:
        self._import_thread = None
        self._import_worker = None
        self._pending_selected_uids = None
        self._pending_side = None
        self._set_import_running(False)

    def _handle_import_finished(
        self, model: ObsModel, units: int, ecs: int, ref_applied: bool
    ) -> None:
        self.set_model(model)
        selected_uids = self._pending_selected_uids
        selected_side = self._pending_side or ""
        self.log.append("Imported DRAGON workbook OK.")
        if selected_uids is not None:
            total = len(selected_uids)
            roots = len(self._dragon_selected_roots or [])
            self.log.append(
                f" - Imported selection: {roots} root unit(s), {total} workbook unit rows."
            )
        assigned = 0
        for unit in _iter_local(self.model.unit_list, "Unit"):
            side_el = jfind(unit, "j:SideSuperior")
            current = side_el.text.strip() if side_el is not None and side_el.text else ""
            if not current and selected_side:
                if side_el is None:
                    side_el = ET.SubElement(unit, jtag("SideSuperior"))
                side_el.text = selected_side
                assigned += 1
        if assigned:
            self.log.append(f" - Applied side {selected_side} to {assigned} units.")
        self.log.append(f" - Units total: {units}")
        self.log.append(f" - EntityCompositions total: {ecs}")
        if ref_applied:
            self.log.append(" - Applied reference UnitDisEnumeration map.")
        meta = (
            getattr(self.model, "_dragon_counts", {}).get("unit_meta")
            if self.model is not None
            else None
        )
        if meta:
            ids_fixed, stamps_fixed, sides_fixed = meta
            self.log.append(
                f" - Unit metadata normalized: ids={ids_fixed}, timestamps={stamps_fixed}, sides set={sides_fixed}"
            )
        self.modelImported.emit(self.model)
        self._cleanup_import_state()

    def _handle_import_failed(self, message: str) -> None:
        self.log.append(f"Import DRAGON failed: {message}")
        QMessageBox.warning(self, "Import DRAGON", f"Failed: {message}")
        self._cleanup_import_state()

    def _handle_import_cancelled(self) -> None:
        self.log.append("Import DRAGON was cancelled.")
        QMessageBox.information(self, "Import DRAGON", "Import cancelled by user.")
        self._cleanup_import_state()

    def set_model(self, model: Optional[ObsModel]):
        self.model = model

    def _on_dragon_path_changed(self, text: str) -> None:
        path = (text or "").strip()
        self.btn_select_units.setEnabled(bool(path))
        if not path:
            self._dragon_tree = None
            self._dragon_tree_path = None
            self._dragon_selected_roots = None
            self.selection_label.setText("Units: ALL")
        elif self._dragon_tree_path and path != self._dragon_tree_path:
            self._dragon_tree = None
            self._dragon_tree_path = None
            self._dragon_selected_roots = None
            self.selection_label.setText("Units: ALL")

    def _ensure_dragon_tree(self, path: str, *, reset_selection: bool = False) -> bool:
        if not path:
            return False
        if self._dragon_tree is not None and self._dragon_tree_path == path:
            return True
        try:
            tree = parse_dragon_unit_hierarchy(path)
        except Exception as exc:
            traceback.print_exc()
            QMessageBox.warning(
                self, "Parse DRAGON Workbook", f"Failed to parse workbook: {exc}"
            )
            return False
        self._dragon_tree = tree
        self._dragon_tree_path = path
        if reset_selection:
            self._dragon_selected_roots = None
            self.selection_label.setText("Units: ALL")
        self.log.append(
            f"Parsed DRAGON workbook: {tree.total_units()} units available."
        )
        return True

    def _resolve_unitclass_master_path(self) -> Path:
        raw = (self.ucl_edit.text() or "").strip()
        if raw:
            resolved = Path(raw).expanduser()
            if resolved.is_dir():
                return resolved / "unitclass-master.xlsx"
            return resolved
        candidates: list[Path] = []
        meipass = getattr(sys, "_MEIPASS", None)
        if meipass:
            try:
                candidates.append(Path(meipass))
            except Exception:
                pass
        try:
            candidates.append(Path(__file__).resolve().parent)
        except Exception:
            pass
        candidates.append(Path.cwd())
        seen: set[Path] = set()
        for base in candidates:
            if not isinstance(base, Path):
                base = Path(base)
            if base in seen:
                continue
            seen.add(base)
            candidate = base / "UnitClass-Masters" / "unitclass-master.xlsx"
            if candidate.exists():
                return candidate
        base = candidates[0] if candidates else Path.cwd()
        if not isinstance(base, Path):
            base = Path(base)
        return base / "UnitClass-Masters" / "unitclass-master.xlsx"

    def on_browse_dragon(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open DRAGON Workbook", "", "Excel Workbook (*.xlsx);;All Files (*)"
        )
        if path:
            self.path_edit.setText(path)
            self._ensure_dragon_tree(path, reset_selection=True)

    def on_browse_refxml(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open reference UnitList XML", "", "OBS XML (*.xml);;All Files (*)"
        )
        if path:
            self.ref_edit.setText(path)

    def on_browse_ecc(self):
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Open EntityCompositionClass master",
            "",
            "Excel (*.xlsx);;All Files (*)",
        )
        if path:
            self.ecc_edit.setText(path)

    def on_browse_ucl(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open UnitClass master", "", "Excel (*.xlsx);;All Files (*)"
        )
        if path:
            self.ucl_edit.setText(path)

    def on_append_unitclasses(self) -> None:
        if cli_append_unitclasses_to_master is None:
            QMessageBox.warning(
                self,
                "Append UnitClass master",
                "DRAGON helper is unavailable in this build.",
            )
            return
        dragon_path = self.path_edit.text().strip()
        if not dragon_path:
            QMessageBox.information(
                self, "Append UnitClass master", "Select a DRAGON workbook first."
            )
            return
        master_path = self._resolve_unitclass_master_path()
        if not (self.ucl_edit.text() or "").strip():
            self.ucl_edit.setText(str(master_path))
        try:
            added = cli_append_unitclasses_to_master(dragon_path, str(master_path))
        except FileNotFoundError as exc:
            QMessageBox.warning(self, "Append UnitClass master", str(exc))
            return
        except ValueError as exc:
            QMessageBox.warning(self, "Append UnitClass master", str(exc))
            return
        except Exception as exc:
            traceback.print_exc()
            QMessageBox.critical(
                self,
                "Append UnitClass master",
                f"Failed to update UnitClass master: {exc}",
            )
            return
        if added:
            msg = f"Appended {added} new UnitClass row(s) to {master_path}"
        else:
            msg = f"No new UnitClass rows were added; {master_path} already contains workbook classes."
        self.log.append(msg)
        QMessageBox.information(self, "Append UnitClass master", msg)

    def on_select_units(self):
        path = self.path_edit.text().strip()
        if not path:
            QMessageBox.information(
                self, "No DRAGON file", "Select a DRAGON workbook first."
            )
            return
        if not self._ensure_dragon_tree(path, reset_selection=False):
            return
        tree = self._dragon_tree
        if tree is None:
            return
        total_root_uids = {node.uid.strip().upper() for node in tree.roots}
        preselected = self._dragon_selected_roots or total_root_uids
        dlg = DragonUnitSelectionDialog(self, tree, preselected)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            chosen = dlg.selected_root_uids()
            if not chosen or chosen == total_root_uids:
                self._dragon_selected_roots = None
                self.selection_label.setText("Units: ALL")
                self.log.append("Unit selection: ALL workbook units will be imported.")
            else:
                self._dragon_selected_roots = chosen
                names = []
                for uid in chosen:
                    node = tree.node_map.get(uid)
                    if node:
                        names.append(node.name or node.uid)
                preview = ", ".join(names[:3])
                if len(names) > 3:
                    preview += ", ..."
                self.selection_label.setText(
                    f"Units: {len(chosen)} root(s) ({preview})"
                )
                self.log.append(f"Unit selection: {len(chosen)} root(s) chosen.")

    def on_build_classes(self):
        if not self.model:
            QMessageBox.information(self, "No model", "Load or create a model first.")
            return
        ecc = self.ecc_edit.text().strip()
        ucl = self.ucl_edit.text().strip()
        try:
            c1 = (
                build_entitycomposition_classlist_from_xlsx(self.model, ecc)
                if ecc
                else 0
            )
            c2 = build_unitclass_list_from_xlsx(self.model, ucl) if ucl else 0
        except Exception as e:
            QMessageBox.warning(self, "Build Classes", f"Failed: {e}")
            return
        self.log.append(f"Built EntityCompositionClassList: {c1}  UnitClassList: {c2}")
        self.modelImported.emit(self.model)

    def on_import(self):
        if self._is_import_running():
            QMessageBox.information(
                self, "Import in progress", "Please wait for the current import to finish."
            )
            return
        path = self.path_edit.text().strip()
        if not path:
            QMessageBox.information(
                self, "No DRAGON file", "Please select a DRAGON .xlsx workbook."
            )
            return
        if self.model is None:
            self.model = _new_blank_model()
        selected_uids: Optional[Set[str]] = None
        if self._dragon_selected_roots:
            if not self._ensure_dragon_tree(path, reset_selection=False):
                return
            tree = self._dragon_tree
            if tree is None:
                return
            selected_uids = tree.gather_subtree_uids(self._dragon_selected_roots)
            if not selected_uids:
                QMessageBox.warning(
                    self, "Import DRAGON", "No units were selected to import."
                )
                return
        side_btn = self.side_group.checkedButton() if hasattr(self, "side_group") else None
        if side_btn is None:
            QMessageBox.information(
                self,
                "Select Side",
                "Please choose BLUFOR, NEUTRAL, or OPFOR for imported units.",
            )
            return
        selected_side = side_btn.text().strip().upper()
        ref_path = self.ref_edit.text().strip() or None
        self._pending_selected_uids = selected_uids
        self._pending_side = selected_side
        self._start_import_worker(path, selected_side, selected_uids, ref_path)

    def _start_import_worker(
        self,
        path: str,
        selected_side: str,
        selected_uids: Optional[Set[str]],
        ref_path: Optional[str],
    ) -> None:
        if self.model is None:
            self.model = _new_blank_model()
        worker = DragonImportWorker(
            self.model,
            path,
            ref_path,
            selected_side,
            selected_uids,
        )
        thread = QThread(self)
        worker.moveToThread(thread)
        thread.started.connect(worker.run)
        worker.progress.connect(self._handle_import_progress)
        worker.finished.connect(self._handle_import_finished)
        worker.failed.connect(self._handle_import_failed)
        worker.cancelled.connect(self._handle_import_cancelled)
        worker.finished.connect(thread.quit)
        worker.failed.connect(thread.quit)
        worker.cancelled.connect(thread.quit)
        thread.finished.connect(thread.deleteLater)
        worker.finished.connect(worker.deleteLater)
        worker.failed.connect(worker.deleteLater)
        worker.cancelled.connect(worker.deleteLater)
        thread.start()
        self._import_thread = thread
        self._import_worker = worker
        self._set_import_running(True)


class LicenseGateDialog(QDialog):

    def __init__(self, parent: Optional[QWidget] = None, *, initial_error: Optional[str] = None):
        super().__init__(parent)
        self.setWindowTitle("OBS Scrubber License Required")
        self._payload: Optional[LicensePayload] = None
        lay = QVBoxLayout(self)
        intro = QLabel(
            "A valid OBS Scrubber license file (.obsl) is required before the tool can run."
        )
        intro.setWordWrap(True)
        lay.addWidget(intro)
        path_row = QHBoxLayout()
        self.path_edit = QLineEdit(self._default_path())
        browse = QPushButton("Browse")
        browse.clicked.connect(self._choose_file)
        path_row.addWidget(self.path_edit, 1)
        path_row.addWidget(browse)
        lay.addLayout(path_row)
        self.status_label = QLabel(initial_error or "Select a license file and click Validate.")
        self.status_label.setWordWrap(True)
        lay.addWidget(self.status_label)
        button_row = QHBoxLayout()
        button_row.addStretch(1)
        self.validate_btn = QPushButton("Validate")
        self.validate_btn.clicked.connect(self._validate)
        self.continue_btn = QPushButton("Continue")
        self.continue_btn.clicked.connect(self.accept)
        self.continue_btn.setEnabled(False)
        cancel_btn = QPushButton("Exit")
        cancel_btn.clicked.connect(self.reject)
        button_row.addWidget(self.validate_btn)
        button_row.addWidget(self.continue_btn)
        button_row.addWidget(cancel_btn)
        lay.addLayout(button_row)
        if initial_error:
            self.status_label.setText(initial_error)

    @property
    def payload(self) -> Optional[LicensePayload]:
        return self._payload

    @staticmethod
    def _default_path() -> str:
        cached = cached_license_path()
        if cached:
            return str(cached)
        return str(Path.cwd() / DEFAULT_LICENSE_FILENAME)

    def _choose_file(self) -> None:
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Select License File",
            self.path_edit.text() or self._default_path(),
            "OBS License (*.obsl);;All Files (*)",
        )
        if path:
            self.path_edit.setText(path)
            self._payload = None
            self.continue_btn.setEnabled(False)

    def _validate(self) -> None:
        candidate = self.path_edit.text().strip()
        if not candidate:
            QMessageBox.warning(self, "License File", "Please select a license file.")
            return
        try:
            payload = load_license_file(candidate)
        except FileNotFoundError:
            QMessageBox.warning(self, "License File", "Selected file does not exist.")
            return
        except LicenseError as exc:
            QMessageBox.critical(self, "License Error", str(exc))
            self.continue_btn.setEnabled(False)
            self._payload = None
            return
        self._payload = payload
        remember_license_path(candidate)
        info = f"{describe_license(payload)}\nSource: {candidate}"
        self.status_label.setText(info)
        self.continue_btn.setEnabled(True)

    def accept(self) -> None:
        if self._payload is None:
            self._validate()
            if self._payload is None:
                return
        super().accept()


class MainWindow(QWidget):

    def __init__(self, license_payload: LicensePayload):
        super().__init__()
        self._license_payload = license_payload
        self.setWindowTitle(
            "ObsScrubber - JTDS OBS XML Analyzer/Scrubber/Generator/Importer"
        )
        self.resize(1080, 720)
        self.tabs = QTabWidget()
        self.tab_an = AnalyzerTab(self)
        self.tab_sc = ScrubberTab(self)
        self.tab_ge = GenerateTab(self)
        self.tab_imp = ImportDragonTab(self)
        self.tabs.addTab(self.tab_an, "1) Analyzer")
        self.tabs.addTab(self.tab_sc, "2) Scrubber")
        self.tabs.addTab(self.tab_ge, "3) Generate")
        self.tabs.addTab(self.tab_imp, "4) Import DRAGON")
        lay = QVBoxLayout(self)
        self.license_label = QLabel(self._license_summary())
        self.license_label.setAlignment(Qt.AlignmentFlag.AlignRight)
        lay.addWidget(self.license_label)
        lay.addWidget(self.tabs)
        self.tab_an.modelLoaded.connect(self.set_model)
        self.tab_imp.modelImported.connect(self.set_model)

    def set_model(self, model: Optional[ObsModel]):
        self.tab_an.set_model(model)
        self.tab_sc.set_model(model)
        self.tab_ge.set_model(model)
        self.tab_imp.set_model(model)

    def _license_summary(self) -> str:
        path_hint = (
            Path(self._license_payload.path).name
            if self._license_payload and self._license_payload.path
            else DEFAULT_LICENSE_FILENAME
        )
        return f"License: {describe_license(self._license_payload)} ({path_hint})"


def _obtain_license(parent: Optional[QWidget] = None) -> Optional[LicensePayload]:
    try:
        return load_first_valid_license()
    except LicenseError as exc:
        dlg = LicenseGateDialog(parent=parent, initial_error=str(exc))
        if dlg.exec() == QDialog.DialogCode.Accepted and dlg.payload:
            return dlg.payload
        return None


def main() -> int:

    app = QApplication(sys.argv)
    license_payload = _obtain_license()
    if license_payload is None:
        QMessageBox.critical(
            None,
            "License Required",
            "A valid OBS Scrubber license (.obsl) is required. The application will now exit.",
        )
        return 1
    global LICENSE_INFO
    LICENSE_INFO = license_payload
    w = MainWindow(license_payload)
    w.show()
    return app.exec()


if __name__ == "__main__":

    sys.exit(main())

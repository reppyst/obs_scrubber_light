#!/usr/bin/env python3
"""Shared utilities for creating and validating OBS Scrubber Light licenses."""

from __future__ import annotations

import base64
import hashlib
import hmac
import json
import os
import secrets
import sys
import uuid
from dataclasses import dataclass
from datetime import datetime, timezone
from os import PathLike
from pathlib import Path
from typing import Any, List, Mapping, Optional, Sequence, Tuple

DEFAULT_LICENSE_FILENAME = "license.obsl"
DEFAULT_PRODUCT = "obs_scrubber_light"
ENV_LICENSE_KEY = "OBS_LICENSE_KEY"
ENV_LICENSE_PATH = "OBS_LICENSE_PATH"
ENV_LICENSE_HOME = "OBS_LICENSE_HOME"
TOKEN_PREFIX = "OBSL1"
PBKDF2_ROUNDS = 200_000
DEFAULT_MASTER_KEY = "obs-scrubber-light|2025|c37276e0dccc4bc5a4acc87d93f19c02"

_CACHE_DIR = Path(
    os.environ.get(ENV_LICENSE_HOME)
    or Path.home() / ".obs_scrubber_light"
)
_CACHE_PATH = _CACHE_DIR / "license_path.json"


class LicenseError(RuntimeError):
    """Raised when license creation or validation fails."""


@dataclass(frozen=True)
class LicensePayload:
    license_id: str
    customer: str
    issued: datetime
    valid_from: datetime
    valid_until: datetime
    note: Optional[str] = None
    products: Tuple[str, ...] = ()
    path: Optional[str] = None

    def to_dict(self) -> Mapping[str, Any]:
        return {
            "schema": "obs-license",
            "schema_version": 1,
            "id": self.license_id,
            "customer": self.customer,
            "issued": _iso(self.issued),
            "valid_from": _iso(self.valid_from),
            "valid_until": _iso(self.valid_until),
            "note": self.note,
            "products": list(self.products),
        }

    @property
    def is_active(self) -> bool:
        now = datetime.now(timezone.utc)
        return self.valid_from <= now <= self.valid_until

    @classmethod
    def from_raw(
        cls,
        data: Mapping[str, Any],
        *,
        path: Optional[str] = None,
    ) -> "LicensePayload":
        schema = data.get("schema")
        version = data.get("schema_version")
        if schema != "obs-license" or version != 1:
            raise LicenseError("License has incompatible schema.")
        try:
            license_id = str(data["id"])
            customer = str(data["customer"]).strip() or "Unspecified"
            issued = _parse_iso(data["issued"])
            valid_from = _parse_iso(data["valid_from"])
            valid_until = _parse_iso(data["valid_until"])
        except KeyError as exc:
            raise LicenseError(f"License payload missing field: {exc.args[0]}") from exc
        except Exception as exc:  # pragma: no cover - defensive
            raise LicenseError(f"License payload invalid: {exc}") from exc
        note = data.get("note")
        products_raw = data.get("products") or []
        products_set = set()
        if isinstance(products_raw, (list, tuple, set)):
            for item in products_raw:
                text = str(item).strip().lower()
                if text:
                    products_set.add(text)
        elif isinstance(products_raw, str):
            text = products_raw.strip().lower()
            if text:
                products_set.add(text)
        products = tuple(sorted(products_set))
        return cls(
            license_id=license_id,
            customer=customer,
            issued=issued,
            valid_from=valid_from,
            valid_until=valid_until,
            note=str(note) if note is not None else None,
            products=products,
            path=path,
        )


def _iso(dt: datetime) -> str:
    return _utc(dt).strftime("%Y-%m-%dT%H:%M:%SZ")


def _parse_iso(value: str) -> datetime:
    if not isinstance(value, str):
        raise LicenseError("Timestamp fields must be ISO strings.")
    text = value.strip()
    if not text:
        raise LicenseError("Timestamp value is empty.")
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(text)
    except ValueError as exc:
        raise LicenseError(f"Invalid timestamp format: {value!r}") from exc
    return _utc(dt)


def _utc(dt: datetime) -> datetime:
    if dt.tzinfo is None:
        return dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


def _resolve_secret(key: Optional[str]) -> str:
    candidate = (key or os.environ.get(ENV_LICENSE_KEY) or DEFAULT_MASTER_KEY).strip()
    if not candidate:
        raise LicenseError(
            "No encryption key provided. Pass key=... or set OBS_LICENSE_KEY."
        )
    return candidate


def _derive_key(secret: str, salt: bytes) -> bytes:
    return hashlib.pbkdf2_hmac(
        "sha256",
        secret.encode("utf-8"),
        salt,
        PBKDF2_ROUNDS,
        dklen=32,
    )


def _xor_stream(data: bytes, derived: bytes, salt: bytes) -> bytes:
    out = bytearray(len(data))
    counter = 0
    offset = 0
    while offset < len(data):
        counter_bytes = counter.to_bytes(8, "big")
        block = hashlib.blake2s(derived + salt + counter_bytes).digest()
        chunk = min(len(block), len(data) - offset)
        for i in range(chunk):
            out[offset + i] = data[offset + i] ^ block[i]
        offset += chunk
        counter += 1
    return bytes(out)


def _b64(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).decode("ascii")


def _b64_decode(text: str) -> bytes:
    return base64.urlsafe_b64decode(text.encode("ascii"))


def _encrypt_payload(payload: Mapping[str, Any], key: Optional[str]) -> str:
    secret = _resolve_secret(key)
    salt = secrets.token_bytes(16)
    derived = _derive_key(secret, salt)
    clear = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")
    cipher = _xor_stream(clear, derived, salt)
    mac = hmac.new(derived, salt + cipher, hashlib.sha256).digest()
    blob = {
        "v": 1,
        "salt": _b64(salt),
        "cipher": _b64(cipher),
        "mac": _b64(mac),
    }
    raw = json.dumps(blob, separators=(",", ":"), sort_keys=True).encode("utf-8")
    token = base64.urlsafe_b64encode(raw).decode("ascii")
    return f"{TOKEN_PREFIX}.{token}"


def _decrypt_payload(token: str, key: Optional[str]) -> Mapping[str, Any]:
    secret = _resolve_secret(key)
    text = token.strip()
    if text.startswith(f"{TOKEN_PREFIX}."):
        text = text.split(".", 1)[1]
    try:
        raw = base64.urlsafe_b64decode(text)
        blob = json.loads(raw.decode("utf-8"))
    except Exception as exc:
        raise LicenseError("License token is corrupted or not base64 data.") from exc
    if blob.get("v") != 1:
        raise LicenseError("Unsupported license blob version.")
    try:
        salt = _b64_decode(blob["salt"])
        cipher = _b64_decode(blob["cipher"])
        mac = _b64_decode(blob["mac"])
    except KeyError as exc:
        raise LicenseError(f"License blob missing field: {exc.args[0]}") from exc
    derived = _derive_key(secret, salt)
    expected_mac = hmac.new(derived, salt + cipher, hashlib.sha256).digest()
    if not hmac.compare_digest(mac, expected_mac):
        raise LicenseError("License token failed integrity verification.")
    clear = _xor_stream(cipher, derived, salt)
    try:
        payload = json.loads(clear.decode("utf-8"))
    except Exception as exc:  # pragma: no cover - defensive
        raise LicenseError("Decrypted license payload is invalid JSON.") from exc
    return payload


def generate_license_token(
    *,
    customer: str,
    start: datetime,
    end: datetime,
    note: Optional[str] = None,
    products: Optional[Sequence[str]] = None,
    key: Optional[str] = None,
) -> Tuple[str, Mapping[str, Any]]:
    start_utc = _utc(start)
    end_utc = _utc(end)
    if end_utc < start_utc:
        raise LicenseError("End date must be on or after the start date.")
    product_set = {DEFAULT_PRODUCT}
    if products:
        for item in products:
            text = str(item).strip().lower()
            if text:
                product_set.add(text)
    payload = {
        "schema": "obs-license",
        "schema_version": 1,
        "id": str(uuid.uuid4()),
        "customer": customer.strip() or "Unspecified",
        "issued": _iso(datetime.now(timezone.utc)),
        "valid_from": _iso(start_utc),
        "valid_until": _iso(end_utc),
        "note": note.strip() if isinstance(note, str) and note.strip() else None,
        "products": sorted(product_set),
    }
    token = _encrypt_payload(payload, key)
    return token, payload


def write_license_file(token: str, destination: PathLike[str] | str) -> Path:
    path = Path(destination).expanduser()
    if not path.suffix:
        path = path.with_suffix(".obsl")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(token.strip() + "\n", encoding="utf-8")
    return path


def load_license_file(
    source: PathLike[str] | str,
    *,
    key: Optional[str] = None,
    require_active: bool = True,
    require_product: Optional[str] = DEFAULT_PRODUCT,
    now: Optional[datetime] = None,
) -> LicensePayload:
    path = Path(source).expanduser()
    if not path.is_file():
        raise FileNotFoundError(path)
    token = path.read_text(encoding="utf-8").strip()
    if not token:
        raise LicenseError(f"License file {path} is empty.")
    payload_dict = _decrypt_payload(token, key)
    payload = LicensePayload.from_raw(payload_dict, path=str(path))
    if require_product:
        product = require_product.strip().lower()
        if product not in payload.products:
            raise LicenseError(
                f"License does not cover product '{require_product}'."
            )
    ref_now = _utc(now or datetime.now(timezone.utc))
    if require_active and not (payload.valid_from <= ref_now <= payload.valid_until):
        raise LicenseError(
            f"License window {payload.valid_from:%Y-%m-%d} to {payload.valid_until:%Y-%m-%d} is not active."
        )
    return payload


def describe_license(payload: LicensePayload | Mapping[str, Any]) -> str:
    if not isinstance(payload, LicensePayload):
        payload = LicensePayload.from_raw(payload)
    start = payload.valid_from.strftime("%Y-%m-%d")
    end = payload.valid_until.strftime("%Y-%m-%d")
    return f"{payload.customer} | valid {start} -> {end}"


def candidate_license_paths(
    additional: Optional[Sequence[PathLike[str] | str]] = None,
) -> List[Path]:
    candidates: List[Path] = []
    env_path = os.environ.get(ENV_LICENSE_PATH)
    if env_path:
        candidates.append(Path(env_path).expanduser())
    cached = cached_license_path()
    if cached:
        candidates.append(cached)
    runtime_dir = _runtime_dir()
    candidates.append(runtime_dir / DEFAULT_LICENSE_FILENAME)
    candidates.append(Path.cwd() / DEFAULT_LICENSE_FILENAME)
    if additional:
        candidates.extend(Path(p).expanduser() for p in additional)
    seen = set()
    unique: List[Path] = []
    for cand in candidates:
        resolved = Path(cand).expanduser()
        key = resolved.resolve(strict=False).as_posix().lower()
        if key in seen:
            continue
        seen.add(key)
        unique.append(resolved)
    return unique


def cached_license_path() -> Optional[Path]:
    try:
        data = json.loads(_CACHE_PATH.read_text(encoding="utf-8"))
        path = data.get("path")
    except FileNotFoundError:
        return None
    except Exception:
        return None
    if not path:
        return None
    candidate = Path(path)
    return candidate if candidate.exists() else None


def remember_license_path(path: PathLike[str] | str) -> None:
    _CACHE_DIR.mkdir(parents=True, exist_ok=True)
    data = {"path": str(Path(path).expanduser())}
    _CACHE_PATH.write_text(json.dumps(data), encoding="utf-8")


def load_first_valid_license(
    *,
    paths: Optional[Sequence[PathLike[str] | str]] = None,
    key: Optional[str] = None,
    require_active: bool = True,
    now: Optional[datetime] = None,
) -> LicensePayload:
    errors: List[str] = []
    for path in candidate_license_paths(paths):
        try:
            payload = load_license_file(
                path,
                key=key,
                require_active=require_active,
                now=now,
            )
        except FileNotFoundError:
            continue
        except LicenseError as exc:
            errors.append(f"{path}: {exc}")
            continue
        remember_license_path(path)
        return payload
    if errors:
        raise LicenseError("No valid license found:\n" + "\n".join(errors))
    raise LicenseError("No license files were found in the known locations.")


def _runtime_dir() -> Path:
    frozen_base = getattr(sys, "_MEIPASS", None)
    if frozen_base:
        return Path(frozen_base)
    return Path(__file__).resolve().parent

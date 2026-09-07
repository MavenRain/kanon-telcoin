#!/usr/bin/env python3
"""Verify the exact metatheory snapshot without consulting another checkout."""

import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
PIN = "c4180626123687858ff83408bab801c6f87e3e71"


def main():
    lock = json.loads((ROOT / "kanon-meta-source.lock.json").read_text())
    if lock["schema"] != 1 or lock["commit"] != PIN:
        raise ValueError("unexpected metatheory source pin or lock schema")
    directory = ROOT / "third_party/kanon_meta"
    expected = lock["files"]
    actual = {str(path.relative_to(directory))
              for path in directory.rglob("*") if path.is_file()}
    if actual != set(expected):
        raise ValueError("metatheory snapshot inventory mismatch")
    for name, row in expected.items():
        digest = hashlib.sha256((directory / name).read_bytes()).hexdigest()
        if digest != row["sha256"]:
            raise ValueError(f"metatheory snapshot hash mismatch: {name}")
    if (ROOT / "lean-toolchain").read_bytes() != (directory / "lean-toolchain").read_bytes():
        raise ValueError("project Lean toolchain differs from the metatheory pin")
    print(f"Verified Kanon metatheory {PIN}: {len(expected)} files")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print(f"metatheory snapshot: {error}", file=sys.stderr)
        sys.exit(1)

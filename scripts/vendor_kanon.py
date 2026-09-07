#!/usr/bin/env python3
"""Import an exact committed source subset, or verify its recorded hashes."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


PIN = "c4180626123687858ff83408bab801c6f87e3e71"
ROOT = Path(__file__).resolve().parent.parent
DEST = ROOT / "third_party" / "kanon"
LOCK = ROOT / "kanon-source.lock.json"


def git(source, *args):
    return subprocess.run(
        ["git", "-C", str(source), *args], check=True, capture_output=True
    ).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--import-from", type=Path)
    args = parser.parse_args()
    if args.import_from is not None:
        if DEST.exists() or LOCK.exists():
            parser.error("snapshot already exists; import never overwrites it")
        names = git(args.import_from, "ls-tree", "-r", "--name-only", PIN).decode().splitlines()
        selected = [
            n for n in names
            if n.startswith(("lib/", "surface/"))
            or n in ("LICENSE-MIT", "LICENSE-APACHE", "SPEC.md")
        ]
        contents = {n: git(args.import_from, "show", f"{PIN}:{n}") for n in selected}
        rows = {}
        for name, data in contents.items():
            path = DEST / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            rows[name] = hashlib.sha256(data).hexdigest()
        LOCK.write_text(json.dumps({
            "schema": 1,
            "upstream": "kanon",
            "commit": PIN,
            "selection": "Committed lib/, surface/, licenses, and SPEC.md; no working-tree changes",
            "sha256": rows,
        }, indent=2, sort_keys=True) + "\n")
    lock = json.loads(LOCK.read_text())
    if lock["commit"] != PIN:
        raise ValueError("unexpected source pin")
    expected = set(lock["sha256"])
    actual = {str(p.relative_to(DEST)) for p in DEST.rglob("*") if p.is_file()}
    if actual != expected:
        raise ValueError(f"snapshot file inventory differs: {sorted(actual ^ expected)}")
    for name, digest in lock["sha256"].items():
        if hashlib.sha256((DEST / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"snapshot hash mismatch: {name}")
    print(f"Verified Kanon {PIN}: {len(expected)} source files")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"snapshot: {error}", file=sys.stderr)
        sys.exit(1)

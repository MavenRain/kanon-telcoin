#!/usr/bin/env python3
"""Compare the checked Kanon fixture's profile with the Lean bridge profile."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def command(arguments, *, source=None):
    result = subprocess.run(arguments, cwd=ROOT, input=source,
                            capture_output=True, timeout=60)
    if result.returncode:
        sys.stderr.buffer.write(result.stdout)
        sys.stderr.buffer.write(result.stderr)
        raise ValueError(f"command failed with exit {result.returncode}: {arguments}")
    return result.stdout.decode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path,
                        default=ROOT / "artifacts/nat-fragment-bridge.json")
    args = parser.parse_args()
    command([sys.executable, "scripts/vendor_kanon.py"])
    command([sys.executable, "scripts/verify_metatheory.py"])
    command(["dune", "build", "tests/nat_fragment.exe"])
    command(["lake", "build", "KanonTelcoin"])
    source_path = ROOT / "foundation/fixtures/nat-fragment.kanon"
    source = source_path.read_bytes()
    actual = json.loads(command(["_build/default/tests/nat_fragment.exe", "--profile"],
                                source=source))
    model = json.loads(command(["lake", "env", "lean", "test/BridgeProfile.lean"]))
    if isinstance(model, str):
        model = json.loads(model)
    if actual != model:
        raise ValueError(f"source adapter and Lean bridge profiles differ: {actual!r} != {model!r}")
    report = {
        "schema": 1,
        "status": "passed",
        "fixture": str(source_path.relative_to(ROOT)),
        "fixture_sha256": hashlib.sha256(source).hexdigest(),
        "profile": actual,
        "scope": "Checked source/schema agreement only; not a proof of OCaml checker or elaborator correctness",
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("PASS checked Kanon source profile agrees with the Lean bridge")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"nat fragment bridge: {error}", file=sys.stderr)
        sys.exit(1)

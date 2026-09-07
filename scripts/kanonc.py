#!/usr/bin/env python3
"""Compile the supported Kanon transition fragment to a bounded EVM counter."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
ABI = [
    {"type": "constructor", "inputs": [], "stateMutability": "nonpayable"},
    {"type": "function", "name": "get", "inputs": [],
     "outputs": [{"name": "state", "type": "uint256"}], "stateMutability": "view"},
    {"type": "function", "name": "increment", "inputs": [],
     "outputs": [{"name": "state", "type": "uint256"}], "stateMutability": "nonpayable"},
    {"type": "event", "name": "Incremented", "anonymous": False,
     "inputs": [{"name": "state", "type": "uint256", "indexed": False}]},
]


def dump(value):
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--entry", default="step")
    parser.add_argument("--bound", type=int, default=1_000_000)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    compiler = ROOT / "_build/default/bin/main.exe"
    if not compiler.is_file():
        parser.error("build the compiler first: dunecho build")
    if not 0 <= args.bound < 2**256:
        parser.error("bound must fit uint256")
    source = args.source.read_bytes()
    if len(source) > 65_536:
        parser.error("prototype source limit is 65536 bytes")
    subprocess.run([sys.executable, str(ROOT / "scripts/vendor_kanon.py")],
                   check=True, stdout=subprocess.DEVNULL)
    completed = subprocess.run([str(compiler), args.entry, str(args.bound)],
                               input=source, capture_output=True, timeout=10)
    if completed.returncode:
        sys.stderr.buffer.write(completed.stderr)
        return completed.returncode
    artifact = json.loads(completed.stdout)
    compiler_sources = [ROOT / "dune", ROOT / "dune-project", ROOT / "bin/dune",
                        ROOT / "lib/dune", *sorted((ROOT / "bin").glob("*.ml")),
                        *sorted((ROOT / "lib").glob("*.ml"))]
    manifest = {
        "schema": 1,
        "compiler": "kanon-telcoin-0.1-prototype",
        "compiler_binary_sha256": sha(compiler.read_bytes()),
        "compiler_source_sha256": {str(path.relative_to(ROOT)): sha(path.read_bytes())
                                   for path in compiler_sources},
        "packager_sha256": sha(Path(__file__).read_bytes()),
        "source_file": args.source.name,
        "source_sha256": sha(source),
        "entry": args.entry,
        "bound": str(args.bound),
        "kanon_source_lock_sha256": sha((ROOT / "kanon-source.lock.json").read_bytes()),
        "target": json.loads((ROOT / "telcoin-target.json").read_text()),
        "runtime_sha256": sha(bytes.fromhex(artifact["runtimeBytecode"][2:])),
        "creation_sha256": sha(bytes.fromhex(artifact["creationBytecode"][2:])),
        "semantics": "Owner-controlled wrapper; checked uint256 intermediates for Nat; saturating NatSub",
        "source_map_granularity": "IR node and wrapper; no surface line mapping",
        "foundation_status": "Kan-only derivation and Lean parity unproved",
        "conformance_status": "Requires validation; emission is not Telcoin execution evidence",
    }
    output_text = {
        "contract.json": dump(artifact),
        "abi.json": dump(ABI),
        "manifest.json": dump(manifest),
        "source-map.json": dump(artifact["sourceMap"]),
        "creation.hex": artifact["creationBytecode"] + "\n",
        "runtime.hex": artifact["runtimeBytecode"] + "\n",
    }
    outputs = {name: text.encode("utf-8") for name, text in output_text.items()}
    outputs["source.kan"] = source
    args.out.mkdir(parents=True, exist_ok=True)
    conflicts = [name for name in outputs if (args.out / name).exists()
                 and (args.out / name).read_bytes() != outputs[name]]
    if conflicts:
        parser.error(f"output differs; choose a new directory: {', '.join(conflicts)}")
    for name, data in outputs.items():
        (args.out / name).write_bytes(data)
    print(f"Compiled {args.source} to {args.out} ({(len(artifact['runtimeBytecode']) - 2) // 2} runtime bytes)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.TimeoutExpired:
        print("kanonc: compiler exceeded the 10-second resource limit", file=sys.stderr)
        sys.exit(2)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"kanonc: {error}", file=sys.stderr)
        sys.exit(2)

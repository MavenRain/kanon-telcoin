#!/usr/bin/env python3
"""Regression checks for byte-preserving packaging and compiler input limits."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "_build/default/bin/main.exe"
PACKAGER = ROOT / "scripts/kanonc.py"
MAX = (1 << 256) - 1


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def invoke(source, *args):
    return subprocess.run([str(BIN), *args], input=source.encode(),
                          capture_output=True, timeout=10)


def main():
    with tempfile.TemporaryDirectory(prefix="kanon-cli-") as directory:
        base = Path(directory)
        path = base / "counter.kan"
        source = ("def step : (state : Nat) -> Nat :=\r\n"
                  "  fun (state : Nat) => natAdd state 1\r\n").encode()
        path.write_bytes(source)
        command = [sys.executable, str(PACKAGER), str(path), "--bound", "3",
                   "--out", str(base / "out")]
        first = subprocess.run(command, capture_output=True, timeout=15)
        require(first.returncode == 0, first.stderr.decode())
        before = {p.name: p.read_bytes() for p in (base / "out").iterdir()}
        again = subprocess.run(command, capture_output=True, timeout=15)
        require(again.returncode == 0, again.stderr.decode())
        after = {p.name: p.read_bytes() for p in (base / "out").iterdir()}
        require(before == after, "identical compilation changed artifacts")
        require(after["source.kan"] == source, "source bytes were not preserved")
        manifest = json.loads(after["manifest.json"])
        require(manifest["source_sha256"] == hashlib.sha256(source).hexdigest(),
                "source hash does not describe packaged source")
        artifact = json.loads(after["contract.json"])
        runtime = bytes.fromhex(artifact["runtimeBytecode"][2:])
        creation = bytes.fromhex(artifact["creationBytecode"][2:])
        require(creation.endswith(runtime), "constructor does not embed the runtime artifact")
        boundaries = {0}
        pc = 0
        while pc < len(runtime):
            opcode = runtime[pc]
            pc += 1 + (opcode - 0x5f if 0x60 <= opcode <= 0x7f else 0)
            boundaries.add(pc)
        require(pc == len(runtime), "runtime ends inside a PUSH operand")
        for span in artifact["sourceMap"]["runtime"]:
            require(span["start"] in boundaries and span["end"] in boundaries
                    and span["start"] <= span["end"], "source-map span is invalid")
        require(artifact["sourceMap"]["source_lines"] is None,
                "prototype invented surface line mapping")
        path.write_bytes(source.replace(b"state 1", b"state 2"))
        changed = subprocess.run(command, capture_output=True, timeout=15)
        require(changed.returncode == 2, "changed output silently overwrote artifacts")
        require(before == {p.name: p.read_bytes() for p in (base / "out").iterdir()},
                "failed conflicting compilation partially changed output")
    print("PASS byte-preserving artifact reruns and conflict refusal")
    print("PASS source-map spans align with emitted instruction boundaries")

    constant = "def step : (state : Nat) -> Nat := fun (state : Nat) => 1\n"
    for state in (str(MAX + 1), "-1", "abc"):
        result = invoke(constant, "--eval", "step", state)
        require(result.returncode == 2 and not result.stdout,
                f"invalid constant-program state accepted: {state}")
    valid = invoke(constant, "--eval", "step", str(MAX))
    require(valid.returncode == 0 and json.loads(valid.stdout) == {"value": "1"},
            "valid unused input was rejected")
    print("PASS reference evaluator validates even unused inputs")

    # Many reused lets have exponential expanded arithmetic size. The compiler
    # must reject this structurally before asking Zarith to evaluate it.
    body = "let x0 : Nat := 2 in "
    for i in range(1, 31):
        body += f"let x{i} : Nat := natMul x{i-1} x{i-1} in "
    source = f"def step : (state : Nat) -> Nat := fun (state : Nat) => {body} x30\n"
    result = invoke(source, "step", "100")
    require(result.returncode == 2 and not result.stdout
            and b"preflight: expanded arithmetic exceeds 4096 nodes"
            in result.stderr.lower(),
            "expanding constant expression was not rejected by syntax preflight")
    print("PASS expensive constant expression rejected before kernel checking")


if __name__ == "__main__":
    main()

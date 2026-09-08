#!/usr/bin/env python3
"""Compare checked kernel evaluation with the bounded arithmetic compiler."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
MAX = (1 << 256) - 1
CAVEAT = (
    "Fixed regression corpus, not a compiler preservation proof. The source "
    "oracle runs the pinned kernel before erasure with natural arithmetic. "
    "The IR checks every arithmetic intermediate against uint256; a source "
    "result that fits uint256 can still require an IR or EVM overflow failure. "
    "Input states are uint256 and both paths retain the frontend resource caps."
)


def source_for(expression):
    return f"def step : (state : Nat) -> Nat := fun (state : Nat) => {expression}\n"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


# Samples are (input, natural result, checked result). The natural result is
# always a number. The checked result is None when the IR must fail with
# intermediate overflow. That includes samples whose natural result fits
# uint256.
CASES = [
    ("identity", "state", [(0, 0, 0), (MAX, MAX, MAX)]),
    ("constant", "7", [(0, 7, 7), (MAX, 7, 7)]),
    ("add_two", "natAdd state 2", [
        (0, 2, 2), (5, 7, 7), (MAX - 2, MAX, MAX), (MAX - 1, MAX + 1, None)]),
    ("saturating_sub", "natSub state 3", [
        (0, 0, 0), (2, 0, 0), (5, 2, 2), (MAX, MAX - 3, MAX - 3)]),
    ("asymmetric_sub", "natSub 10 state", [(0, 10, 10), (3, 7, 7), (12, 0, 0)]),
    ("multiply", "natMul state 7", [
        (0, 0, 0), (3, 21, 21), (MAX // 7, (MAX // 7) * 7, (MAX // 7) * 7),
        (MAX // 7 + 1, (MAX // 7 + 1) * 7, None)]),
    ("multiply_zero_right", "natMul state 0", [(0, 0, 0), (MAX, 0, 0)]),
    ("multiply_zero_left", "natMul 0 state", [(0, 0, 0), (MAX, 0, 0)]),
    ("asymmetric_nested", "natSub 20 (natMul state 3)", [(2, 14, 14), (9, 0, 0)]),
    ("intermediate_overflow", "natSub (natAdd state 1) 1", [
        (0, 0, 0), (MAX, MAX, None)]),
    ("zero_does_not_erase_overflow", "natMul 0 (natAdd state 1)", [
        (2, 0, 0), (MAX, 0, None)]),
    ("unused_let_still_evaluates", "let discarded : Nat := natAdd state 1 in 0", [
        (2, 0, 0), (MAX, 0, None)]),
    ("max_add_boundary", f"natAdd state {MAX}", [
        (0, MAX, MAX), (1, MAX + 1, None)]),
    ("max_mul_boundary", f"natMul state {MAX}", [
        (0, 0, 0), (1, MAX, MAX), (2, 2 * MAX, None)]),
    ("shared_let", "let x : Nat := natAdd state 1 in natMul x x", [
        (0, 1, 1), (3, 16, 16), (MAX, (MAX + 1) ** 2, None)]),
    ("shadow_state", "let state : Nat := natAdd state 2 in natSub state 1", [
        (0, 1, 1), (5, 6, 6), (MAX, MAX + 1, None)]),
    ("nested_shadow", "let x : Nat := natAdd state 3 in "
        "let y : Nat := (let x : Nat := 2 in natMul x 4) in natSub x y", [
        (0, 0, 0), (10, 5, 5), (MAX, MAX - 5, None)]),
    ("repeated_binding", "let x : Nat := natAdd state 1 in "
        "let x : Nat := natMul x 2 in natSub x state", [
        (0, 2, 2), (5, 7, 7), (MAX, MAX + 2, None)]),
    ("closed_unused_overflow", f"let ignored : Nat := natAdd {MAX} 1 in state", [
        (0, 0, None), (MAX, MAX, None)]),
    ("annotated_arithmetic", "((natSub state 4 : Nat) : Nat)", [
        (0, 0, 0), (9, 5, 5), (MAX, MAX - 4, MAX - 4)]),
]


def validate_corpus(cases):
    """Lint the table once, so no per-sample run repeats a table check."""
    for name, _expression, samples in cases:
        for state, natural, checked in samples:
            require(0 <= state <= MAX, f"{name}: input state {state} is outside uint256")
            require(checked is None or checked == natural,
                    f"{name} at {state}: the corpus predicts disagreement "
                    "on a successful IR result")


validate_corpus(CASES)


# The authored compiler files. The harness hashes this list, so a new file in
# bin/ or lib/ must be added here and counted in VALIDATION.md.
COMPILER_SOURCES = [
    "dune",
    "dune-project",
    "bin/dune",
    "lib/dune",
    "bin/main.ml",
    "lib/contract_ir.ml",
    "lib/evm.ml",
    "lib/frontend.ml",
    "lib/nat_fragment.ml",
]


def invoke(compiler, source, *args):
    return subprocess.run([str(compiler), *args], input=source, text=True,
                          capture_output=True, timeout=10, check=False)


def expect_value(result, mode, state, expected):
    require(result.returncode == 0 and not result.stderr,
            f"{mode} at {state}: {result.stderr}")
    require(json.loads(result.stdout) == {"value": str(expected)},
            f"{mode} at {state}: {result.stdout} != {expected}")
    return {"status": "value", "value": str(expected)}


def expect_overflow(result, mode, state):
    require(result.returncode == 2 and not result.stdout
            and "overflow" in result.stderr.lower(),
            f"{mode} at {state}: expected overflow, got {result}")
    return {"status": "intermediate_overflow"}


def evaluate(compiler, source, state, natural, checked):
    source_result = invoke(compiler, source, "--eval-source", "step", str(state))
    source_observation = expect_value(source_result, "--eval-source", state, natural)
    ir_result = invoke(compiler, source, "--eval", "step", str(state))
    ir_observation = (expect_overflow(ir_result, "--eval", state) if checked is None
                      else expect_value(ir_result, "--eval", state, checked))
    return {"state": str(state), "source": source_observation, "ir": ir_observation}


def refusals(compiler):
    # Every fixture pins the intended refusal reason. A refusal for another
    # reason must fail the check, because every refusal exits 2 with stderr.
    constant = source_for("1")
    fixtures = [
        (constant, "step", "-1", "invalid integer: -1"),
        (constant, "step", "abc", "invalid integer: abc"),
        (constant, "step", str(MAX + 1), "input state is outside uint256"),
        (constant, "missing", "0", "no source definition named missing"),
        ("def step : Nat := 0\n", "step", "0", "mismatch: the term has type nat"),
        ("axiom trusted : Nat\n" + constant, "step", "0", "user axiom"),
        (constant + constant, "step", "0", "a declaration repeats name step"),
        (source_for(f"{MAX + 1}"), "step", "0",
            "a nat literal is outside the uint256 range"),
        (source_for("let f : Nat -> Nat := fun (x : Nat) => x in f state"), "step", "0",
            "a type annotation other than bare nat"),
        (source_for("unknown"), "step", "0", "global or unbound value unknown"),
        (source_for("(" * 129 + "state" + ")" * 129), "step", "0",
            "parenthesis nesting exceeds 128"),
        (" " * 65_537 + constant, "step", "0", "the source exceeds 65536 bytes"),
    ]
    expanding = "let x0 : Nat := 2 in "
    for index in range(1, 31):
        expanding += f"let x{index} : Nat := natMul x{index - 1} x{index - 1} in "
    fixtures.append((source_for(expanding + "x30"), "step", "0",
                     "expanded arithmetic exceeds 4096 nodes"))
    for source, entry, state, diagnostic in fixtures:
        result = invoke(compiler, source, "--eval-source", entry, state)
        require(result.returncode == 2 and not result.stdout
                and diagnostic in result.stderr.lower(),
                f"source oracle refused for another reason: {entry}, {state}, "
                f"{result.returncode}, {result.stderr}")
    # Selection is exercised separately from the default entry in the corpus.
    renamed = constant.replace("def step", "def advance")
    selected = invoke(compiler, renamed, "--eval-source", "advance", str(MAX))
    require(selected.returncode == 0 and not selected.stderr
            and json.loads(selected.stdout) == {"value": "1"},
            "source oracle ignored the selected entry")
    return len(fixtures)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "_build/default/bin/main.exe")
    parser.add_argument("--report", type=Path, default=ROOT / "artifacts/source-differential.json")
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    report = {"schema": 1, "status": "running", "caveat": CAVEAT, "cases": [],
              "corpus_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    started = time.monotonic()
    try:
        report["compiler_sha256"] = hashlib.sha256(compiler.read_bytes()).hexdigest()
        authored = sorted(str(path.relative_to(ROOT)) for path in
                          [*(ROOT / "bin").glob("*.ml"), *(ROOT / "lib").glob("*.ml")])
        require(authored == sorted(name for name in COMPILER_SOURCES
                                   if name.endswith(".ml")),
                "authored OCaml file set changed: update COMPILER_SOURCES and VALIDATION.md")
        report["compiler_source_sha256"] = {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in COMPILER_SOURCES
        }
        report["kanon_source_lock_sha256"] = hashlib.sha256(
            (ROOT / "kanon-source.lock.json").read_bytes()).hexdigest()
        for name, expression, samples in CASES:
            source = source_for(expression)
            result = invoke(compiler, source, "step", str(MAX))
            require(result.returncode == 0 and not result.stderr,
                    f"{name}: compilation failed: {result.stderr}")
            artifact = json.loads(result.stdout)
            observations = [evaluate(compiler, source, *sample) for sample in samples]
            report["cases"].append({
                "name": name, "source": source,
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "runtime_sha256": hashlib.sha256(bytes.fromhex(
                    artifact["runtimeBytecode"][2:])).hexdigest(),
                "samples": observations,
            })
            print(f"PASS {name}: {len(samples)} source/IR samples", flush=True)
        report["refusal_checks"] = refusals(compiler)
        report["status"] = "passed"
    # Any failure must reach the report. A malformed artifact raises a TypeError
    # here, and an unwritten report leaves a stale earlier report in artifacts/.
    except Exception as error:
        report["status"] = "failed"
        report["failure"] = f"{type(error).__name__}: {error}"
        print(report["failure"], file=sys.stderr)
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        report["sample_count"] = sum(len(case["samples"]) for case in report["cases"])
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(f"{report['status'].upper()}: {args.report}")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())

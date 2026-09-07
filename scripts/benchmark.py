#!/usr/bin/env python3
"""Calibrate one tiny workload; this is not an OCaml compilation-parity gate."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent.parent
BOUND = 1_000_000
LABELS = ("packaged_kanon", "raw_kanon", "ocamlc_zarith", "ocamlopt_zarith")
REFERENCE = r'''type error = Intermediate_overflow | Bound_exceeded

let max_word = Z.pred (Z.shift_left Z.one 256)
let bound = Z.of_int 1000000

let checked value =
  if Z.sign value < 0 || Z.gt value max_word then Error Intermediate_overflow
  else Ok value

let step state =
  Result.bind (checked state) (fun state ->
    Result.bind (checked (Z.add state Z.one)) (fun next ->
      if Z.gt next bound then Error Bound_exceeded else Ok next))

let error_text error =
  match error with
  | Intermediate_overflow -> "intermediate-overflow"
  | Bound_exceeded -> "bound-exceeded"

let main state =
  Result.fold
    ~ok:(fun value -> print_endline (Z.to_string value))
    ~error:(fun error -> prerr_endline (error_text error); exit 2)
    (step state)

let decimal text =
  if String.length text = 0 then None
  else String.fold_left
    (fun parsed character ->
      Option.bind parsed (fun value ->
        if character >= '0' && character <= '9' then
          Some (Z.add (Z.mul value (Z.of_int 10))
                (Z.of_int (Char.code character - Char.code '0')))
        else None))
    (Some Z.zero) text

let () =
  if Array.length Sys.argv <> 2 then exit 64
  else
    Option.fold
      ~none:(fun () -> exit 64)
      ~some:(fun state () -> main state)
      (decimal Sys.argv.(1)) ()
'''


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def run(command, *, env, cwd=ROOT, data=None, timeout=60):
    return subprocess.run(command, cwd=cwd, env=env, input=data,
                          capture_output=True, timeout=timeout, check=False)


def require_success(completed, label):
    if completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace")[-4000:]
        raise RuntimeError(f"{label} exited {completed.returncode}: {detail}")
    return completed


def tool_path(name, directory=None, required=True):
    candidate = directory / name if directory else None
    found = str(candidate) if candidate and candidate.is_file() else shutil.which(name)
    if directory and required and not (candidate and candidate.is_file()):
        raise RuntimeError(f"{name} is absent from requested toolchain {directory}")
    if not found:
        if required:
            raise RuntimeError(f"{name} is not installed or is not on PATH")
        return None
    return Path(found).absolute()


def text_command(command, env):
    return require_success(run(command, env=env), " ".join(map(str, command))).stdout.decode().strip()


def discover(toolchain):
    ocamlc = tool_path("ocamlc", toolchain)
    ocamlopt = tool_path("ocamlopt", toolchain)
    ocamlfind = tool_path("ocamlfind", toolchain, required=False)
    env = os.environ.copy()
    env["PYTHONSAFEPATH"] = "1"
    env["PATH"] = os.pathsep.join(dict.fromkeys(
        [str(ocamlc.parent), str(ocamlopt.parent), env.get("PATH", "")]))
    where = Path(text_command([str(ocamlc), "-where"], env))
    if ocamlfind:
        zarith = Path(text_command([str(ocamlfind), "query", "zarith"], env))
        zarith_version = text_command(
            [str(ocamlfind), "query", "-format", "%v", "zarith"], env)
    else:
        choices = [where / "zarith", where]
        zarith = next((path for path in choices if (path / "z.cmi").is_file()), None)
        if zarith is None:
            raise RuntimeError(f"cannot locate installed Zarith beneath {where}")
        zarith_version = "unavailable without ocamlfind; archive hashes recorded"
    for name in ("z.cmi", "zarith.cma", "zarith.cmxa"):
        if not (zarith / name).is_file():
            raise RuntimeError(f"missing installed Zarith artifact: {zarith / name}")
    versions = {
        "python": {"path": sys.executable, "version": platform.python_version()},
        "ocamlc": {"path": str(ocamlc), "version": text_command([str(ocamlc), "-version"], env),
                   "sha256": sha256(ocamlc.read_bytes())},
        "ocamlopt": {"path": str(ocamlopt), "version": text_command([str(ocamlopt), "-version"], env),
                     "sha256": sha256(ocamlopt.read_bytes())},
        "zarith": {"path": str(zarith), "version": zarith_version,
                   "archive_sha256": {name: sha256((zarith / name).read_bytes())
                                      for name in ("zarith.cma", "zarith.cmxa")}},
    }
    if ocamlfind:
        versions["ocamlfind"] = {
            "path": str(ocamlfind), "version": text_command(
                [str(ocamlfind), "query", "-format", "%v", "findlib"], env),
            "sha256": sha256(ocamlfind.read_bytes()),
        }
    return {"ocamlc": ocamlc, "ocamlopt": ocamlopt, "ocamlfind": ocamlfind,
            "zarith": zarith, "env": env, "versions": versions}


def compiler_command(name, tools, directory):
    source = directory / "reference.ml"
    executable = directory / "reference.exe"
    if tools["ocamlfind"]:
        command = [str(tools["ocamlfind"]), name, "-package", "zarith", "-linkpkg"]
    else:
        archive = "zarith.cma" if name == "ocamlc" else "zarith.cmxa"
        command = [str(tools[name]), "-I", str(tools["zarith"]),
                   str(tools["zarith"] / archive)]
    return command + [str(source), "-o", str(executable)]


def verify_reference(executable, env):
    cases = [("0", 0, b"1\n", b""),
             (str(BOUND - 1), 0, f"{BOUND}\n".encode(), b""),
             (str(BOUND), 2, b"", b"bound-exceeded\n"),
             (str(2**256 - 1), 2, b"", b"intermediate-overflow\n")]
    for state, code, stdout, stderr in cases:
        completed = run([str(executable), state], env=env)
        if (completed.returncode, completed.stdout, completed.stderr) != (code, stdout, stderr):
            raise RuntimeError(f"OCaml reference disagrees at state {state}")


def verify_kanon(compiler, source, env):
    for state in (0, 1, BOUND - 1):
        completed = require_success(run(
            [str(compiler), "--eval", "step", str(state)], env=env, data=source),
            "Kanon arithmetic calibration check")
        if json.loads(completed.stdout).get("value") != str(state + 1):
            raise RuntimeError("examples/counter.kan no longer matches the increment reference")


def summary(samples):
    ordered = sorted(samples)
    return {"samples_ms": samples, "median_ms": statistics.median(samples),
            "p95_ms": ordered[math.ceil(len(ordered) * 0.95) - 1],
            "min_ms": ordered[0], "max_ms": ordered[-1]}


def benchmark(args):
    source_path = ROOT / "examples/counter.kan"
    source = source_path.read_bytes()
    compiler = ROOT / "_build/default/bin/main.exe"
    if not compiler.is_file():
        raise RuntimeError("build _build/default/bin/main.exe before benchmarking")
    tools = discover(args.toolchain)
    env = tools["env"]
    verify_kanon(compiler, source, env)
    timings = []
    with tempfile.TemporaryDirectory(prefix="kanon-telcoin-benchmark-") as temporary:
        work = Path(temporary)
        for round_index in range(args.warmups + args.runs):
            phase = "warmup" if round_index < args.warmups else "measured"
            offset = round_index % len(LABELS)
            order = LABELS[offset:] + LABELS[:offset]
            for order_index, label in enumerate(order):
                directory = work / f"round-{round_index:02d}-{label}"
                directory.mkdir()
                data = None
                if label == "packaged_kanon":
                    command = [sys.executable, "-P", str(ROOT / "scripts/kanonc.py"),
                               str(source_path), "--bound", str(BOUND),
                               "--out", str(directory / "artifact")]
                elif label == "raw_kanon":
                    command = [str(compiler), "step", str(BOUND)]
                    data = source
                else:
                    (directory / "reference.ml").write_text(REFERENCE)
                    command = compiler_command(label.split("_")[0], tools, directory)
                started = time.perf_counter_ns()
                completed = run(command, env=env, data=data, cwd=directory)
                elapsed_ms = (time.perf_counter_ns() - started) / 1_000_000
                require_success(completed, label)
                if label == "raw_kanon":
                    artifact = json.loads(completed.stdout)
                    if not artifact.get("creationBytecode", "").startswith("0x"):
                        raise RuntimeError("raw compiler did not emit an artifact")
                elif label == "packaged_kanon":
                    if not (directory / "artifact/manifest.json").is_file():
                        raise RuntimeError("packaged compiler did not emit its manifest")
                elif round_index == 0:
                    verify_reference(directory / "reference.exe", env)
                timings.append({"label": label, "phase": phase, "round": round_index,
                                "order_in_round": order_index, "elapsed_ms": elapsed_ms,
                                "command": [argument.replace(str(work), "<temporary>")
                                            for argument in command],
                                "returncode": completed.returncode})
    results = {label: summary([row["elapsed_ms"] for row in timings
                              if row["label"] == label and row["phase"] == "measured"])
               for label in LABELS}
    ratios = {f"{subject}_over_{baseline}": results[subject]["median_ms"] / results[baseline]["median_ms"]
              for subject in ("packaged_kanon", "raw_kanon")
              for baseline in ("ocamlc_zarith", "ocamlopt_zarith")}
    sources = {"kanon": {"path": "examples/counter.kan", "sha256": sha256(source)},
               "ocaml": {"source": REFERENCE, "sha256": sha256(REFERENCE.encode())},
               "compiler_binary_sha256": sha256(compiler.read_bytes()),
               "benchmark_script_sha256": sha256(Path(__file__).read_bytes()),
               "packaging_script_sha256": sha256((ROOT / "scripts/kanonc.py").read_bytes())}
    for path in ("kanon-source.lock.json", "telcoin-target.json"):
        if (ROOT / path).is_file():
            sources[path] = sha256((ROOT / path).read_bytes())
    return {
        "schema": 1, "classification": "calibration_only_not_ocaml_parity_gate",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "host": {"os": platform.platform(), "machine": platform.machine(),
                 "processor": platform.processor(), "cpu_count": os.cpu_count(),
                 "load_average_at_end": list(os.getloadavg()) if hasattr(os, "getloadavg") else None},
        "tools": tools["versions"], "sources": sources,
        "settings": {"bound": BOUND, "warmups_per_label": args.warmups,
                     "measured_runs_per_label": args.runs, "timeout_per_command_seconds": 60,
                     "order": "rotate the four labels by one position each round",
                     "percentile_method": "nearest rank; with seven samples p95 is the maximum"},
        "measurement_scope": {
            "packaged_kanon": "Python startup, source-lock verification, compiler, ABI/manifest/bytecode/source-map artifact writes; fresh output directory each time",
            "raw_kanon": "Compiler process startup, parse, elaboration, checking, erasure, EVM emission and JSON output; source passed on stdin",
            "ocamlc_zarith": "Bytecode compiler invocation and executable link with existing Zarith; fresh source and build directory",
            "ocamlopt_zarith": "Native compiler invocation and executable link with existing Zarith; fresh source and build directory",
            "excluded": "Tool discovery, source preparation, correctness spot checks, report serialization and prototype compiler build",
        },
        "timings": timings, "results": results, "informational_median_ratios": ratios,
        "caveats": [
            "This is a calibration of one tiny increment program, not an OCaml speed-parity gate.",
            "There is no frozen representative workload corpus or matched ABI/artifact workload here.",
            "OCaml reference checks uint256 intermediates and the final bound, but omits the EVM ABI, storage, authorization and event wrapper.",
            "All compilers reuse installed dependencies and warm filesystem caches; baseline outputs use fresh directories.",
            "Short measurements are sensitive to process startup, filesystem cache, host load, scheduling, power state and thermal behavior.",
            "Interleaving reduces order bias; it does not remove noise. No CPU pinning or machine isolation is imposed.",
            "Ratios are informational. None establishes Lean parity, Kan-only foundations, or general OCaml compilation-speed parity.",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--runs", type=int, default=7)
    parser.add_argument("--toolchain", type=Path,
                        help="pin ocamlc/ocamlopt to this bin directory; default uses PATH")
    parser.add_argument("--out", type=Path, default=ROOT / "artifacts/benchmark.json")
    args = parser.parse_args()
    if not 0 <= args.warmups <= 10 or not 1 <= args.runs <= 50:
        parser.error("warmups must be 0..10 and runs must be 1..50")
    report = benchmark(args)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Calibration only, no parity gate: {args.out}")
    for label in LABELS:
        result = report["results"][label]
        print(f"{label}: median={result['median_ms']:.3f} ms p95={result['p95_ms']:.3f} ms")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"benchmark: {error}", file=sys.stderr)
        sys.exit(2)

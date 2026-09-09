#!/usr/bin/env python3
"""Compare packaging implementations with identical inputs; calibration only."""

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
BASELINE_REF = "c8b0ea51469f323577310c50c17963ea9bd70185"
BOUND = 1_000_000
LABELS = ("baseline", "candidate")
WORKLOADS = ("counter.kan", "step_two.kan", "shared_let.kan")
SCRIPTS = ("scripts/kanonc.py", "scripts/vendor_kanon.py")
COMPILER = "_build/default/bin/main.exe"
ARTIFACTS = ("creation.hex", "runtime.hex", "contract.json", "abi.json",
             "source-map.json", "source.kan", "manifest.json")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def run(command, *, cwd=ROOT, env=None, timeout=60):
    completed = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                               timeout=timeout, check=False)
    if completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace")[-2000:]
        raise RuntimeError(f"command exited {completed.returncode}: {command[0]}: {detail}")
    return completed


def git(*arguments):
    return run(["git", "-C", str(ROOT), *arguments]).stdout


def compiler_sources():
    return ["dune", "dune-project", "bin/dune", "lib/dune",
            *[str(path.relative_to(ROOT)) for directory in ("bin", "lib")
              for path in sorted((ROOT / directory).glob("*.ml"))]]


def input_paths():
    return [COMPILER, *compiler_sources(), "kanon-source.lock.json",
            "telcoin-target.json", *[f"examples/{name}" for name in WORKLOADS],
            *[str(path.relative_to(ROOT))
              for path in sorted((ROOT / "third_party/kanon").rglob("*"))
              if path.is_file()]]


def hashes(root, names):
    return {name: sha256((root / name).read_bytes()) for name in names}


def prepare(work, baseline_ref):
    commit = git("rev-parse", "--verify", "--end-of-options",
                 f"{baseline_ref}^{{commit}}").decode().strip()
    names = input_paths()
    if not (ROOT / COMPILER).is_file():
        raise RuntimeError(f"build {COMPILER} before benchmarking")
    common = work / "inputs"
    for name in names:
        destination = common / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, destination)
    common_hashes = hashes(common, names)
    roots = {}
    script_hashes = {}
    for label in LABELS:
        root = work / label
        shutil.copytree(common, root)
        for name in SCRIPTS:
            data = git("show", f"{commit}:{name}") if label == "baseline" else (ROOT / name).read_bytes()
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        if hashes(root, names) != common_hashes:
            raise RuntimeError(f"{label} input snapshot differs")
        roots[label] = root
        script_hashes[label] = hashes(root, SCRIPTS)
    return commit, roots, common_hashes, script_hashes


def read_artifacts(directory, label, workload, script_hashes, input_hashes, target):
    inventory = {str(path.relative_to(directory)) for path in directory.rglob("*")}
    if inventory != set(ARTIFACTS):
        raise RuntimeError(f"{label}/{workload}: artifact inventory differs: {sorted(inventory)}")
    contents = {name: (directory / name).read_bytes() for name in ARTIFACTS}
    manifest = json.loads(contents["manifest.json"])
    if not isinstance(manifest, dict):
        raise ValueError(f"{label}/{workload}: manifest must be an object")
    if manifest.pop("packager_sha256", None) != script_hashes["scripts/kanonc.py"]:
        raise RuntimeError(f"{label}/{workload}: packager hash is incorrect")
    verifier_key = "source_verifier_sha256"
    if label == "candidate" and verifier_key not in manifest:
        raise RuntimeError(f"{label}/{workload}: verifier hash is absent")
    if verifier_key in manifest:
        if manifest.pop(verifier_key) != script_hashes["scripts/vendor_kanon.py"]:
            raise RuntimeError(f"{label}/{workload}: verifier hash is incorrect")
    expected = {
        "compiler_binary_sha256": input_hashes[COMPILER],
        "compiler_source_sha256": {name: input_hashes[name] for name in compiler_sources()},
        "kanon_source_lock_sha256": input_hashes["kanon-source.lock.json"],
        "source_file": workload,
        "source_sha256": input_hashes[f"examples/{workload}"],
        "entry": "step",
        "bound": str(BOUND),
        "target": target,
        "runtime_sha256": sha256(bytes.fromhex(contents["runtime.hex"].decode().strip()[2:])),
        "creation_sha256": sha256(bytes.fromhex(contents["creation.hex"].decode().strip()[2:])),
    }
    for name, value in expected.items():
        if manifest.get(name) != value:
            raise RuntimeError(f"{label}/{workload}: manifest {name} differs from measured inputs")
    if sha256(contents["source.kan"]) != input_hashes[f"examples/{workload}"]:
        raise RuntimeError(f"{label}/{workload}: source bytes differ")
    artifact_hashes = {name: sha256(data) for name, data in contents.items()}
    comparable = {name: data for name, data in contents.items() if name != "manifest.json"}
    comparable["manifest.json"] = manifest
    return comparable, artifact_hashes


def summary(samples, unit):
    ordered = sorted(samples)
    return {f"samples_{unit}": samples,
            f"median_{unit}": statistics.median(samples),
            f"p95_{unit}": ordered[math.ceil(len(ordered) * 0.95) - 1],
            f"min_{unit}": ordered[0], f"max_{unit}": ordered[-1]}


def load_average():
    return list(os.getloadavg()) if hasattr(os, "getloadavg") else None


def benchmark(args):
    started_at = datetime.now(timezone.utc).isoformat()
    load_start = load_average()
    env = os.environ.copy()
    env["PYTHONSAFEPATH"] = "1"
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    timings = []
    pairs = []
    artifact_evidence = {}
    with tempfile.TemporaryDirectory(prefix="kanon-telcoin-packaging-") as temporary:
        work = Path(temporary)
        commit, roots, input_hashes, script_hashes = prepare(work, args.baseline_ref)
        target = json.loads((work / "inputs/telcoin-target.json").read_bytes())
        for round_index in range(args.warmups + args.runs):
            phase = "warmup" if round_index < args.warmups else "measured"
            order = LABELS if round_index % 2 == 0 else tuple(reversed(LABELS))
            offset = round_index % len(WORKLOADS)
            workload_order = WORKLOADS[offset:] + WORKLOADS[:offset]
            for workload_index, workload in enumerate(workload_order):
                outputs = {}
                elapsed = {}
                for order_index, label in enumerate(order):
                    root = roots[label]
                    sample = work / "samples" / f"{round_index:02d}" / workload / label
                    sample.mkdir(parents=True)
                    output = sample / "artifact"
                    command = [sys.executable, "-P", str(root / "scripts/kanonc.py"),
                               str(root / "examples" / workload), "--entry", "step",
                               "--bound", str(BOUND), "--out", str(output)]
                    start = time.perf_counter_ns()
                    completed = run(command, cwd=sample, env=env)
                    elapsed[label] = (time.perf_counter_ns() - start) / 1_000_000
                    outputs[label] = output
                    timings.append({
                        "workload": workload, "label": label, "phase": phase,
                        "round": round_index, "workload_order_in_round": workload_index,
                        "order_in_pair": order_index, "elapsed_ms": elapsed[label],
                        "command": [argument.replace(str(work), "<temporary>") for argument in command],
                        "cwd": str(sample).replace(str(work), "<temporary>"),
                        "returncode": completed.returncode,
                    })
                comparable = {}
                for label in LABELS:
                    comparable[label], observed = read_artifacts(
                        outputs[label], label, workload, script_hashes[label], input_hashes, target)
                    prior = artifact_evidence.setdefault(workload, {}).setdefault(label, observed)
                    if prior != observed:
                        raise RuntimeError(f"{label}/{workload}: repeated artifacts are nondeterministic")
                for name in ARTIFACTS:
                    if comparable["baseline"][name] != comparable["candidate"][name]:
                        raise RuntimeError(f"{workload}: baseline and candidate differ in {name}")
                pairs.append({"workload": workload, "phase": phase, "round": round_index,
                              "order": list(order), "baseline_ms": elapsed["baseline"],
                              "candidate_ms": elapsed["candidate"],
                              "candidate_over_baseline": elapsed["candidate"] / elapsed["baseline"],
                              "all_seven_artifacts_verified": True})
        for label in LABELS:
            if hashes(roots[label], list(input_hashes)) != input_hashes:
                raise RuntimeError(f"{label}: measured input snapshot changed during calibration")
            if hashes(roots[label], SCRIPTS) != script_hashes[label]:
                raise RuntimeError(f"{label}: measured scripts changed during calibration")
    results = {}
    for workload in WORKLOADS:
        measured = [row for row in pairs if row["workload"] == workload and row["phase"] == "measured"]
        by_label = {label: summary([row[f"{label}_ms"] for row in measured], "ms") for label in LABELS}
        results[workload] = {
            **by_label,
            "paired_candidate_over_baseline": summary([row["candidate_over_baseline"] for row in measured], "ratio"),
            "candidate_median_over_baseline_median": by_label["candidate"]["median_ms"] / by_label["baseline"]["median_ms"],
        }
    return {
        "schema": 1,
        "classification": "paired_packaging_calibration_only_no_performance_gate",
        "timestamp_utc": started_at,
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        "baseline": {"requested_ref": args.baseline_ref, "resolved_commit": commit,
                     "scope": "Only the two packaging scripts come from this commit; all other inputs use the same current snapshot."},
        "provenance": {"common_input_sha256": input_hashes, "script_sha256": script_hashes,
                       "benchmark_script_sha256": sha256(Path(__file__).read_bytes())},
        "python": {"executable": sys.executable, "version": platform.python_version(),
                   "full_version": sys.version, "implementation": platform.python_implementation(),
                   "executable_sha256": sha256(Path(sys.executable).read_bytes())},
        "host": {"os": platform.platform(), "machine": platform.machine(),
                 "processor": platform.processor(), "cpu_count": os.cpu_count(),
                 "load_average_at_start": load_start, "load_average_at_end": load_average()},
        "settings": {"bound": BOUND, "entry": "step", "workloads": list(WORKLOADS),
                     "warmups_per_label_per_workload": args.warmups,
                     "measured_runs_per_label_per_workload": args.runs,
                     "timeout_per_command_seconds": 60,
                     "environment_overrides": {"PYTHONSAFEPATH": "1", "PYTHONDONTWRITEBYTECODE": "1"},
                     "order": "Alternate baseline/candidate order each round; rotate workload order each round.",
                     "percentile_method": "Nearest rank: sorted samples at ceil(n * 0.95) - 1.",
                     "parallelism": "One packaged compilation at a time."},
        "measurement_scope": {
            "included": "Python startup, full source-lock verification, compiler startup/checking/emission, and all seven artifact writes into a fresh output directory.",
            "excluded": "Compiler build, snapshot preparation and hashing, baseline extraction, artifact comparison, and report serialization.",
            "cache_state": "Existing dependencies and filesystem caches reused; all private input snapshots copied before timing; every output directory is fresh.",
        },
        "artifact_comparison": {
            "files": list(ARTIFACTS),
            "rule": "Six files must match byte-for-byte. Parsed manifests must match after removing only packager_sha256 and source_verifier_sha256.",
            "provenance_rule": "Every packager hash and each present verifier hash must match the actual script. The candidate verifier hash is required; the baseline may predate it.",
            "determinism": "Every repetition must have the same seven artifact hashes for its label and workload.",
            "sha256": artifact_evidence,
        },
        "timings": timings, "pairs": pairs, "results": results,
        "caveats": [
            "This is a packaging calibration on three small existing arithmetic workloads, with no timing-based pass threshold.",
            "It does not establish an OCaml compilation-speed, Lean parity, Kan foundation, or Telcoin conformance claim.",
            "Both script versions use one identical current compiler/input snapshot; this does not compare complete historical compiler versions.",
            "Warm filesystem caches and installed dependencies are reused. Cold or incremental compiler builds are outside this measurement.",
            "Host load, scheduling, power state, and thermal behavior can affect short process measurements. No CPU pinning or machine isolation is imposed.",
            "Alternating paired runs reduces order bias but does not remove measurement noise; ratios are informational.",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-ref", default=BASELINE_REF)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--runs", type=int, default=9)
    parser.add_argument("--out", type=Path, default=ROOT / "artifacts/packaging-benchmark.json")
    args = parser.parse_args()
    if not 0 <= args.warmups <= 10 or not 1 <= args.runs <= 50:
        parser.error("warmups must be 0..10 and runs must be 1..50")
    report = benchmark(args)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Packaging calibration only, no performance gate: {args.out}")
    for workload, result in report["results"].items():
        print(f"{workload}: baseline={result['baseline']['median_ms']:.3f} ms "
              f"candidate={result['candidate']['median_ms']:.3f} ms "
              f"paired median ratio={result['paired_candidate_over_baseline']['median_ratio']:.3f}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"benchmark-packaging: {error}", file=sys.stderr)
        sys.exit(2)

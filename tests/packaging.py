#!/usr/bin/env python3
"""Check artifact provenance and source verification in isolated fixture copies."""

from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "_build/default/bin/main.exe"
SOURCE = (b"def step : (state : Nat) -> Nat :=\r\n"
          b"  fun (state : Nat) => natAdd state 1\r\n")
OUTPUT_NAMES = {
    "contract.json", "abi.json", "manifest.json", "source-map.json",
    "creation.hex", "runtime.hex", "source.kan",
}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def output_bytes(directory):
    return {path.name: path.read_bytes() for path in directory.iterdir()}


def copy_fixture(base):
    fixture = base / "project"
    fixture.mkdir()
    for name in ("dune", "dune-project", "kanon-source.lock.json", "telcoin-target.json"):
        shutil.copy2(ROOT / name, fixture / name)
    for name in ("bin", "lib", "third_party/kanon"):
        shutil.copytree(ROOT / name, fixture / name)
    (fixture / "scripts").mkdir()
    for name in ("kanonc.py", "vendor_kanon.py"):
        shutil.copy2(ROOT / "scripts" / name, fixture / "scripts" / name)
    compiler = fixture / "_build/default/bin/main.exe"
    compiler.parent.mkdir(parents=True)
    compiler.symlink_to(BIN)
    (fixture / "counter.kan").write_bytes(SOURCE)
    return fixture


def command_line(fixture, script, args, safe_flag, safe_env):
    env = os.environ.copy()
    env.pop("PYTHONSAFEPATH", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    if safe_env:
        env["PYTHONSAFEPATH"] = "1"
    command = [sys.executable]
    if safe_flag:
        command.append("-P")
    command.extend([str(fixture / "scripts" / script), *map(str, args)])
    return command, env


def invoke(fixture, cwd, script, *args, safe_flag=False, safe_env=False):
    command, env = command_line(fixture, script, args, safe_flag, safe_env)
    return subprocess.run(command, cwd=cwd, env=env, capture_output=True, timeout=15)


def spawn_packager(fixture, cwd, out, bound):
    command, env = command_line(fixture, "kanonc.py",
                                (fixture / "counter.kan", "--bound", bound, "--out", out),
                                True, True)
    return subprocess.Popen(command, cwd=cwd, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def package(fixture, cwd, out, **options):
    return invoke(fixture, cwd, "kanonc.py", fixture / "counter.kan",
                  "--bound", "3", "--out", out, **options)


def check_artifacts(fixture, contents):
    require(set(contents) == OUTPUT_NAMES, "packaging did not publish exactly seven artifacts")
    require(contents["source.kan"] == SOURCE, "CRLF source bytes were not preserved")
    artifact = json.loads(contents["contract.json"])
    manifest = json.loads(contents["manifest.json"])
    runtime = bytes.fromhex(artifact["runtimeBytecode"][2:])
    creation = bytes.fromhex(artifact["creationBytecode"][2:])
    require(contents["runtime.hex"] == (artifact["runtimeBytecode"] + "\n").encode(),
            "runtime.hex differs from contract.json")
    require(contents["creation.hex"] == (artifact["creationBytecode"] + "\n").encode(),
            "creation.hex differs from contract.json")
    require(json.loads(contents["source-map.json"]) == artifact["sourceMap"],
            "source-map.json differs from contract.json")
    require(isinstance(json.loads(contents["abi.json"]), list), "ABI is not a JSON array")
    source_paths = {"dune", "dune-project", "bin/dune", "lib/dune"}
    source_paths.update(str(path.relative_to(fixture))
                        for directory in ("bin", "lib")
                        for path in (fixture / directory).glob("*.ml"))
    hashes = {
        "source_sha256": sha(SOURCE),
        "compiler_binary_sha256": sha(BIN.read_bytes()),
        "compiler_source_sha256": {
            name: sha((fixture / name).read_bytes()) for name in source_paths
        },
        "packager_sha256": sha((fixture / "scripts/kanonc.py").read_bytes()),
        "source_verifier_sha256": sha((fixture / "scripts/vendor_kanon.py").read_bytes()),
        "kanon_source_lock_sha256": sha((fixture / "kanon-source.lock.json").read_bytes()),
        "runtime_sha256": sha(runtime),
        "creation_sha256": sha(creation),
    }
    require({name: value for name, value in manifest.items() if name.endswith("_sha256")}
            == hashes, "manifest hashes do not describe the packaged inputs and outputs")
    require(manifest["source_file"] == "counter.kan" and manifest["entry"] == "step"
            and manifest["bound"] == "3", "manifest lost compilation parameters")
    require(manifest["target"] == json.loads((fixture / "telcoin-target.json").read_bytes()),
            "manifest does not describe the configured target")


@contextmanager
def replaced(path, data):
    previous = path.read_bytes() if path.exists() else None
    if data is None:
        path.unlink()
    else:
        path.write_bytes(data)
    try:
        yield
    finally:
        if previous is None:
            path.unlink()
        else:
            path.write_bytes(previous)


def check_rejection(fixture, cwd, existing, baseline, fresh, diagnostic, label):
    vendor = invoke(fixture, cwd, "vendor_kanon.py", safe_flag=True, safe_env=True)
    require(vendor.returncode == 1 and not vendor.stdout and diagnostic in vendor.stderr,
            f"standalone verifier accepted {label}: {vendor.stderr.decode()}")
    require(vendor.stderr.startswith(b"snapshot: ") and b"Traceback" not in vendor.stderr,
            f"standalone verifier did not report {label} through its own diagnostic: "
            f"{vendor.stderr.decode()}")
    for out in (existing, fresh):
        result = package(fixture, cwd, out, safe_flag=True, safe_env=True)
        require(result.returncode == 2 and not result.stdout and diagnostic in result.stderr,
                f"packager accepted {label}: {result.stderr.decode()}")
        require(result.stderr.startswith(b"kanonc: ") and b"Traceback" not in result.stderr,
                f"packager did not report {label} through its own diagnostic: "
                f"{result.stderr.decode()}")
        require(output_bytes(existing) == baseline, f"{label} changed existing artifacts")
        require(not fresh.exists(), f"{label} published an output directory")


def main():
    require(BIN.is_file(), "build the compiler first: dunecho build")
    with tempfile.TemporaryDirectory(prefix="kanon-packaging-") as directory:
        base = Path(directory)
        fixture = copy_fixture(base)
        unrelated = base / "unrelated"
        unrelated.mkdir()
        existing = base / "out"
        first = package(fixture, fixture, existing)
        require(first.returncode == 0,
                f"packaging the pristine fixture failed: rc={first.returncode} "
                f"{first.stderr.decode()}")
        baseline = output_bytes(existing)
        check_artifacts(fixture, baseline)
        for safe_flag, safe_env in ((False, False), (True, False), (False, True), (True, True)):
            result = package(fixture, unrelated, existing,
                             safe_flag=safe_flag, safe_env=safe_env)
            require(result.returncode == 0,
                    f"safe-path rerun failed with -P={safe_flag}, PYTHONSAFEPATH={safe_env}: "
                    f"rc={result.returncode} {result.stderr.decode()}")
            require(output_bytes(existing) == baseline,
                    f"rerun changed bytes with -P={safe_flag}, PYTHONSAFEPATH={safe_env}")
        fresh = base / "fresh"
        result = package(fixture, unrelated, fresh, safe_flag=True, safe_env=True)
        require(result.returncode == 0,
                f"packaging into a fresh directory failed: rc={result.returncode} "
                f"{result.stderr.decode()}")
        require(output_bytes(fresh) == baseline, "fresh output directory changed artifact bytes")
        print("PASS seven artifacts, complete provenance hashes, CRLF bytes, "
              "deterministic reruns from an unrelated working directory")

        shadow = fixture / "scripts/hashlib.py"
        poison = b'raise AssertionError("loaded hashlib from the script directory")\n'
        with replaced(shadow, poison):
            shadowed = base / "shadowed"
            result = package(fixture, unrelated, shadowed)
            require(result.returncode != 0 and b"loaded hashlib" in result.stderr,
                    f"module shadowing in the script directory was not loaded without a safe "
                    f"path: rc={result.returncode} {result.stderr.decode()}")
            require(not shadowed.exists(), "module shadowing published an output directory")
            for index, (safe_flag, safe_env) in enumerate(((True, False), (False, True))):
                out = base / f"unshadowed-{index}"
                result = package(fixture, unrelated, out, safe_flag=safe_flag, safe_env=safe_env)
                require(result.returncode == 0,
                        f"module shadowing survived -P={safe_flag}, "
                        f"PYTHONSAFEPATH={safe_env}: rc={result.returncode} "
                        f"{result.stderr.decode()}")
                require(output_bytes(out) == baseline,
                        f"module shadowing changed artifact bytes under -P={safe_flag}, "
                        f"PYTHONSAFEPATH={safe_env}")
        print("PASS a shadowing module beside the scripts is ignored under -P and PYTHONSAFEPATH")

        with replaced(fixture / "counter.kan", SOURCE.replace(b"state 1", b"state 2")):
            result = package(fixture, unrelated, existing, safe_flag=True)
            require(result.returncode == 2 and b"output differs" in result.stderr,
                    "conflicting compilation was not refused")
            require(output_bytes(existing) == baseline, "conflict partially changed artifacts")
        print("PASS conflicting output is refused without changing artifacts")

        verifier_path = fixture / "scripts/vendor_kanon.py"
        with replaced(verifier_path, verifier_path.read_bytes() + b"\ndef broken(:\n"):
            unreadable = base / "unreadable"
            result = package(fixture, unrelated, unreadable, safe_flag=True, safe_env=True)
            require(result.returncode == 2 and b"source verifier is unreadable" in result.stderr
                    and b"Traceback" not in result.stderr,
                    f"a corrupt source verifier was not reported through the packager "
                    f"diagnostic: rc={result.returncode} {result.stderr.decode()}")
            require(not unreadable.exists(),
                    "a corrupt source verifier published an output directory")
        print("PASS a corrupt source verifier is refused with the documented exit code")

        race = base / "race"
        workers = [spawn_packager(fixture, unrelated, race, bound) for bound in (3, 4)]
        for worker in workers:
            worker.communicate(timeout=60)
        codes = [worker.returncode for worker in workers]
        require(codes.count(0) == 1 and codes.count(2) == 1,
                f"concurrent packagers into one directory did not serialise: exit codes {codes}")
        published = output_bytes(race)
        require(set(published) == OUTPUT_NAMES,
                f"concurrent packaging left a partial directory: {sorted(published)}")
        artifact = json.loads(published["contract.json"])
        runtime_digest = sha(bytes.fromhex(artifact["runtimeBytecode"][2:]))
        manifest = json.loads(published["manifest.json"])
        require(manifest["runtime_sha256"] == runtime_digest
                and published["runtime.hex"] == (artifact["runtimeBytecode"] + "\n").encode(),
                f"concurrent packagers mixed artifacts: manifest runtime_sha256 "
                f"{manifest['runtime_sha256']} does not hash the published runtime bytecode "
                f"{runtime_digest}")
        print("PASS concurrent packagers publish one consistent artifact set")

        vendor = invoke(fixture, unrelated, "vendor_kanon.py", safe_flag=True, safe_env=True)
        require(vendor.returncode == 0 and b"Verified Kanon" in vendor.stdout,
                f"standalone verifier did not report a verified snapshot: "
                f"rc={vendor.returncode} stdout={vendor.stdout!r} {vendor.stderr.decode()}")
        lock_path = fixture / "kanon-source.lock.json"
        lock = json.loads(lock_path.read_bytes())
        source_path = fixture / "third_party/kanon/lib/term.ml"
        wrong_pin = dict(lock, commit="0" * 40)
        missing_pin = {name: value for name, value in lock.items() if name != "commit"}
        mutations = [
            ("changed source content", source_path, source_path.read_bytes() + b"\n",
             b"snapshot hash mismatch"),
            ("extra snapshot file", source_path.parent / "unexpected.ml", b"unexpected\n",
             b"snapshot file inventory differs"),
            ("missing snapshot file", source_path, None, b"snapshot file inventory differs"),
            ("wrong source pin", lock_path, json.dumps(wrong_pin).encode(),
             b"unexpected source pin"),
            # The decoder text belongs to the standard library, so this row relies on
            # the exit codes and the diagnostic prefix checked in check_rejection.
            ("malformed JSON lock", lock_path, b"{invalid JSON\n", b""),
            ("missing lock pin", lock_path, json.dumps(missing_pin).encode(), b"commit"),
            ("list-shaped lock", lock_path, json.dumps([lock]).encode(),
             b"malformed source lock"),
            ("list-shaped lock hashes", lock_path,
             json.dumps(dict(lock, sha256=sorted(lock["sha256"]))).encode(),
             b"malformed source lock"),
        ]
        for index, (label, path, data, diagnostic) in enumerate(mutations):
            with replaced(path, data):
                check_rejection(fixture, unrelated, existing, baseline,
                                base / f"unpublished-{index}", diagnostic, label)
            print(f"PASS {label} rejected by packager and standalone verifier before publication")
        restored = package(fixture, unrelated, existing, safe_flag=True, safe_env=True)
        require(restored.returncode == 0,
                f"restored snapshot did not package: rc={restored.returncode} "
                f"{restored.stderr.decode()}")
        require(output_bytes(existing) == baseline, "restored fixture changed artifact bytes")
        print("PASS restored snapshot verifies and reproduces the original artifacts")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exercise the prototype against a fresh owned Anvil process on loopback."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import traceback
from urllib.error import URLError
from urllib.request import ProxyHandler, Request, build_opener


ROOT = Path(__file__).resolve().parents[1]
MAX_WORD = (1 << 256) - 1
DEFAULT_SOURCE = (
    "def step : (state : Nat) -> Nat := "
    "fun (state : Nat) => natAdd state 1\n"
)
CAVEAT = (
    "This is a local baseline EVM test using the recorded Anvil version and its "
    "Prague mode. It does not establish conformance to a pinned Telcoin Network "
    "client, genesis, execution dependencies, precompiles, or live network. "
    "The IR comparison uses partial uint256 execution with checked intermediate "
    "results, not unrestricted natural-number computation or a compiler proof."
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


class RpcError(RuntimeError):
    def __init__(self, method: str, error: dict):
        self.method = method
        self.error = error
        super().__init__(f"{method}: {json.dumps(error, sort_keys=True)}")


class LocalNode:
    def __init__(self, executable: str):
        self.executable = executable
        self.process = None
        self.log = None
        self.request_id = 0
        self.opener = build_opener(ProxyHandler({}))
        self.command = []

    def __enter__(self):
        # Reserve a loopback port briefly; monitor the child for a bind failure.
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as reservation:
            reservation.bind(("127.0.0.1", 0))
            port = reservation.getsockname()[1]
        self.url = f"http://127.0.0.1:{port}"
        self.command = [
            self.executable, "--host", "127.0.0.1", "--port", str(port),
            "--hardfork", "prague", "--chain-id", "2017", "--accounts", "2",
            "--threads", "2", "--quiet",
        ]
        self.log = tempfile.TemporaryFile(mode="w+b")
        try:
            self.process = subprocess.Popen(
                self.command, stdin=subprocess.DEVNULL,
                stdout=self.log, stderr=subprocess.STDOUT,
            )
            deadline = time.monotonic() + 15
            while time.monotonic() < deadline:
                if self.process.poll() is not None:
                    self.log.seek(0)
                    raise RuntimeError(
                        "owned Anvil exited during startup: "
                        + self.log.read(8192).decode(errors="replace")
                    )
                try:
                    if self.rpc("eth_chainId") == "0x7e1":
                        require(self.process.poll() is None, "owned Anvil exited")
                        return self
                except (URLError, TimeoutError, ConnectionError):
                    pass
                time.sleep(0.05)
            raise RuntimeError("owned Anvil did not start within 15 seconds")
        except BaseException:
            self.close()
            raise

    def close(self):
        if self.process is not None and self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=5)
        if self.log is not None:
            self.log.close()

    def __exit__(self, _kind, _value, _traceback):
        self.close()

    def rpc(self, method: str, params=None):
        self.request_id += 1
        request = Request(
            self.url,
            data=json.dumps({
                "jsonrpc": "2.0", "id": self.request_id,
                "method": method, "params": [] if params is None else params,
            }).encode(),
            headers={"Content-Type": "application/json"},
        )
        with self.opener.open(request, timeout=5) as response:
            result = json.load(response)
        if "error" in result:
            raise RpcError(method, result["error"])
        return result["result"]

    def receipt(self, tx_hash: str):
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            receipt = self.rpc("eth_getTransactionReceipt", [tx_hash])
            if receipt is not None:
                return receipt
            time.sleep(0.02)
        raise RuntimeError(f"no receipt for local transaction {tx_hash}")

    def send(self, transaction: dict):
        transaction = {"gas": "0x989680", **transaction}
        return self.receipt(self.rpc("eth_sendTransaction", [transaction]))


class Suite:
    def __init__(self, compiler: Path, report: dict):
        self.compiler = compiler
        self.report = report

    def record(self, name: str, **evidence):
        self.report["checks"].append({"name": name, "status": "passed", **evidence})
        print(f"PASS {name}", flush=True)

    def invoke(self, source: str, arguments: list[str]):
        return subprocess.run(
            [str(self.compiler), *arguments], input=source, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20,
            cwd=ROOT, check=False,
        )

    def compile(self, source: str, bound: int = MAX_WORD):
        result = self.invoke(source, ["step", str(bound)])
        require(result.returncode == 0, f"compile failed: {result.stderr}")
        require(not result.stderr, f"successful compile wrote stderr: {result.stderr}")
        artifact = json.loads(result.stdout)
        for field in ("creationBytecode", "runtimeBytecode"):
            value = artifact.get(field)
            require(isinstance(value, str) and value.startswith("0x"), f"missing {field}")
            require(len(bytes.fromhex(value[2:])) > 0, f"empty {field}")
        require(isinstance(artifact.get("sourceMap"), dict), "missing source map")
        return artifact

    def eval(self, source: str, state: int, expected: int | None):
        result = self.invoke(source, ["--eval", "step", str(state)])
        if expected is None:
            require(result.returncode == 2, f"overflow eval accepted: {result.stdout}")
            require(not result.stdout.strip(), "overflow eval emitted a result")
            require("overflow" in result.stderr.lower(), result.stderr)
        else:
            require(result.returncode == 0, f"IR evaluation failed: {result.stderr}")
            require(json.loads(result.stdout) == {"value": str(expected)}, result.stdout)

    def negative_compilation(self):
        boolean_type = "sum ((prod () : Type 0), (prod () : Type 0))"
        negative_cases = [
            ("wrong_entry_type", "def step : Nat := 0\n", "step", None),
            ("ill_typed_body", source_for("()"), "step", None),
            ("unknown_entry", DEFAULT_SOURCE, "absent", "no source definition"),
            ("user_axiom", "axiom trusted : Nat\n" + DEFAULT_SOURCE,
             "step", "unsupported: preflight: user axiom"),
            ("unsupported_boolean", source_for(
                f"let b : {boolean_type} := natEq state 0 in state"),
             "step", "unsupported:"),
            ("unsupported_closure", source_for(
                "let f : Nat -> Nat := fun (x : Nat) => natAdd x state in f 1"),
             "step", "unsupported:"),
            ("literal_exceeds_uint256", source_for(str(MAX_WORD + 1)),
             "step", "uint256 range"),
        ]
        for name, source, entry, diagnostic in negative_cases:
            result = self.invoke(source, [entry, "100"])
            require(result.returncode == 2, f"{name}: expected exit 2, got {result.returncode}")
            require(not result.stdout.strip(), f"{name}: failure emitted an artifact")
            require(bool(result.stderr.strip()), f"{name}: missing diagnostic")
            require("parse" not in result.stderr.lower(), f"{name}: malformed test syntax")
            if diagnostic is not None:
                require(diagnostic in result.stderr.lower(), f"{name}: {result.stderr}")
            self.record(name, diagnostic=result.stderr.strip())

    def deploy(self, node: LocalNode, owner: str, artifact: dict):
        receipt = node.send({"from": owner, "data": artifact["creationBytecode"]})
        require(int(receipt["status"], 16) == 1, "deployment reverted")
        address = receipt["contractAddress"]
        require(bool(address), "deployment receipt has no contract address")
        installed = node.rpc("eth_getCode", [address, "latest"])
        require(installed.lower() == artifact["runtimeBytecode"].lower(),
                "installed runtime differs from compiler artifact")
        require(storage(node, address, 0) == int(owner, 16), "constructor owner slot mismatch")
        return address

    def contracts(self, node: LocalNode):
        accounts = node.rpc("eth_accounts")
        require(len(accounts) == 2, "expected exactly two local accounts")
        owner, outsider = accounts
        selector = lambda name: node.rpc("web3_sha3", ["0x" + name.encode().hex()])[:10]
        get = selector("get()")
        inc = selector("increment()")
        topic = node.rpc("web3_sha3", ["0x" + b"Incremented(uint256)".hex()])
        require(get == "0x6d4ce63c" and inc == "0xd09de08a", "ABI selector mismatch")
        artifact = self.compile(DEFAULT_SOURCE, 3)
        require(artifact == self.compile(DEFAULT_SOURCE, 3), "compilation is nondeterministic")
        failed_creation = node.send({"from": owner, "data": artifact["creationBytecode"],
                                     "value": "0x1"})
        check_failure(failed_creation)
        failed_address = failed_creation.get("contractAddress")
        if failed_address:
            require(node.rpc("eth_getCode", [failed_address, "latest"]) == "0x",
                    "failed nonpayable constructor installed code")
        self.record("nonpayable_constructor")
        address = self.deploy(node, owner, artifact)
        self.record("deployment_and_reproducibility", address=address,
                    runtime_bytes=(len(artifact["runtimeBytecode"]) - 2) // 2)
        require(call_word(node, owner, address, get) == 0, "initial counter is nonzero")
        require(call_word(node, outsider, address, get) == 0, "public get rejected outsider")
        self.record("initial_state_and_public_get")
        require(call_word(node, owner, address, inc) == 1, "increment preview is wrong")
        require(storage(node, address, 1) == 0, "eth_call persisted state")
        self.eval(DEFAULT_SOURCE, 0, 1)
        receipt = node.send({"from": owner, "to": address, "data": inc})
        check_success(receipt)
        require(storage(node, address, 1) == 1, "increment did not persist")
        require(call_word(node, owner, address, get) == 1, "get disagrees with storage")
        check_event(receipt, address, topic, 1)
        self.record("increment_result_state_event", event_topic=topic)

        reject_call(node, {"from": outsider, "to": address, "data": inc})
        receipt = node.send({"from": outsider, "to": address, "data": inc})
        check_failure(receipt)
        require(storage(node, address, 1) == 1, "unauthorized call changed state")
        self.record("unauthorized_increment_rollback")

        for calldata in ("0x", "0x00", inc[:8], "0xffffffff", get + "00", inc + "00"):
            reject_call(node, {"from": owner, "to": address, "data": calldata})
        receipt = node.send({"from": owner, "to": address, "data": inc + "00"})
        check_failure(receipt)
        require(storage(node, address, 1) == 1, "malformed call changed state")
        self.record("malformed_calldata_and_unknown_selector")

        for calldata in (get, inc):
            reject_call(node, {"from": owner, "to": address, "data": calldata, "value": "0x1"})
        receipt = node.send({"from": owner, "to": address, "data": inc, "value": "0x1"})
        check_failure(receipt)
        require(storage(node, address, 1) == 1, "value-bearing call changed state")
        require(int(node.rpc("eth_getBalance", [address, "latest"]), 16) == 0,
                "rejected call retained value")
        self.record("nonpayable_calls_rollback")

        # Repeat the same nonzero-to-nonzero update with one fewer gas unit.
        receipt = node.send({"from": owner, "to": address, "data": inc})
        check_success(receipt)
        check_event(receipt, address, topic, 2)
        used_gas = int(receipt["gasUsed"], 16)
        seed_state(node, address, 1)
        receipt = node.send({"from": owner, "to": address, "data": inc,
                             "gas": hex(used_gas - 1)})
        check_failure(receipt)
        require(storage(node, address, 1) == 1, "out-of-gas failed to roll back storage")
        self.record("low_gas_rollback", successful_gas=used_gas, failed_gas=used_gas - 1)

        for expected in (2, 3):
            require(call_word(node, owner, address, inc) == expected, "bound preview mismatch")
            receipt = node.send({"from": owner, "to": address, "data": inc})
            check_success(receipt)
            check_event(receipt, address, topic, expected)
        reject_call(node, {"from": owner, "to": address, "data": inc})
        receipt = node.send({"from": owner, "to": address, "data": inc})
        check_failure(receipt)
        require(storage(node, address, 1) == 3, "bound exhaustion changed state")
        self.record("bound_exhaustion_rollback")
        self.arithmetic(node, owner, get, inc, topic)

    def arithmetic(self, node, owner, get, inc, topic):
        cases = [
            ("add_two", "natAdd state 2", [(0, 2), (5, 7), (MAX_WORD - 2, MAX_WORD),
                                             (MAX_WORD - 1, None)]),
            ("saturating_sub", "natSub state 3", [(0, 0), (2, 0), (5, 2),
                                                   (MAX_WORD, MAX_WORD - 3)]),
            ("asymmetric_sub", "natSub 10 state", [(0, 10), (3, 7), (12, 0)]),
            ("multiply", "natMul state 7", [(0, 0), (3, 21),
                (MAX_WORD // 7, (MAX_WORD // 7) * 7), (MAX_WORD // 7 + 1, None)]),
            ("multiply_zero_right", "natMul state 0", [(0, 0), (MAX_WORD, 0)]),
            ("multiply_zero_left", "natMul 0 state", [(0, 0), (MAX_WORD, 0)]),
            ("asymmetric_nested", "natSub 20 (natMul state 3)", [(2, 14), (9, 0)]),
            ("intermediate_overflow", "natSub (natAdd state 1) 1",
             [(0, 0), (MAX_WORD, None)]),
            ("zero_does_not_erase_overflow", "natMul 0 (natAdd state 1)",
             [(2, 0), (MAX_WORD, None)]),
            ("unused_let_still_evaluates", "let discarded : Nat := natAdd state 1 in 0",
             [(2, 0), (MAX_WORD, None)]),
            ("max_add_boundary", f"natAdd state {MAX_WORD}", [(0, MAX_WORD), (1, None)]),
            ("max_mul_boundary", f"natMul state {MAX_WORD}",
             [(0, 0), (1, MAX_WORD), (2, None)]),
        ]
        runtimes = set()
        for name, expression, samples in cases:
            source = source_for(expression)
            artifact = self.compile(source)
            runtimes.add(artifact["runtimeBytecode"])
            address = self.deploy(node, owner, artifact)
            observations = []
            for state, expected in samples:
                seed_state(node, address, state)
                require(call_word(node, owner, address, get) == state, "test state seed failed")
                self.eval(source, state, expected)
                transaction = {"from": owner, "to": address, "data": inc}
                if expected is None:
                    reject_call(node, transaction)
                    receipt = node.send(transaction)
                    check_failure(receipt)
                    require(storage(node, address, 1) == state, f"{name}: overflow changed state")
                else:
                    actual = call_word(node, owner, address, inc)
                    require(actual == expected, f"{name} at {state}: {actual} != {expected}")
                    receipt = node.send(transaction)
                    check_success(receipt)
                    require(storage(node, address, 1) == expected, f"{name}: persisted result wrong")
                    check_event(receipt, address, topic, expected)
                observations.append({"state": str(state),
                                     "expected": None if expected is None else str(expected)})
            self.record(name, source=source.strip(),
                        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                        samples=observations)
        require(len(runtimes) >= 8, "source changes did not drive distinct emitted programs")
        self.record("source_drives_bytecode", distinct_runtimes=len(runtimes))


def source_for(expression: str) -> str:
    return f"def step : (state : Nat) -> Nat := fun (state : Nat) => {expression}\n"


def storage(node, address, slot):
    return int(node.rpc("eth_getStorageAt", [address, hex(slot), "latest"]), 16)


def seed_state(node, address, value):
    # Test-only mutation of the fresh owned node, never a deployment workflow.
    node.rpc("anvil_setStorageAt", [address, "0x" + f"{1:064x}", "0x" + f"{value:064x}"])
    require(storage(node, address, 1) == value, "anvil_setStorageAt did not set state")


def call_word(node, sender, address, data):
    result = node.rpc("eth_call", [{"from": sender, "to": address, "data": data}, "latest"])
    require(isinstance(result, str) and len(result) == 66, f"invalid uint256 ABI result: {result}")
    return int(result, 16)


def reject_call(node, transaction):
    try:
        node.rpc("eth_call", [transaction, "latest"])
    except RpcError as error:
        require("revert" in str(error).lower() or "out of gas" in str(error).lower(),
                f"unexpected RPC failure instead of EVM failure: {error}")
        return
    raise AssertionError(f"invalid local call succeeded: {transaction}")


def check_success(receipt):
    require(int(receipt["status"], 16) == 1, f"transaction failed: {receipt['transactionHash']}")


def check_failure(receipt):
    require(int(receipt["status"], 16) == 0, f"transaction unexpectedly succeeded: {receipt}")
    require(receipt["logs"] == [], "reverted transaction retained logs")


def check_event(receipt, address, topic, value):
    require(len(receipt["logs"]) == 1, "expected exactly one Incremented event")
    event = receipt["logs"][0]
    require(event["address"].lower() == address.lower(), "event address mismatch")
    require([entry.lower() for entry in event["topics"]] == [topic.lower()],
            f"Incremented(uint256) topic mismatch: {event['topics']}")
    require(event["data"].lower() == "0x" + f"{value:064x}", "event payload mismatch")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "_build/default/bin/main.exe")
    parser.add_argument("--report", type=Path, default=ROOT / "artifacts/evm-validation.json")
    args = parser.parse_args()
    report = {
        "status": "running", "checks": [], "caveat": CAVEAT,
        "network_scope": "fresh owned Anvil subprocess, 127.0.0.1 only",
        "chain_id": 2017, "hardfork": "prague",
        "state_seeding": "anvil_setStorageAt is used only for local edge-case fixtures",
    }
    started = time.monotonic()
    try:
        require(args.compiler.is_file(), f"compiler is missing: {args.compiler}")
        executable = shutil.which("anvil")
        require(executable is not None, "anvil is not installed")
        version = subprocess.run([executable, "--version"], capture_output=True,
                                 text=True, timeout=10, check=True)
        report["anvil_version"] = version.stdout.strip()
        report["compiler_sha256"] = hashlib.sha256(args.compiler.read_bytes()).hexdigest()
        suite = Suite(args.compiler.resolve(), report)
        suite.negative_compilation()
        with LocalNode(executable) as node:
            report["anvil_command"] = node.command
            report["client_version"] = node.rpc("web3_clientVersion")
            suite.contracts(node)
        report["status"] = "passed"
    except Exception as error:
        report["status"] = "failed"
        report["failure"] = f"{type(error).__name__}: {error}"
        traceback.print_exc()
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        report["passed_checks"] = len(report["checks"])
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(f"{report['status'].upper()}: {args.report}", flush=True)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())

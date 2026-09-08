# Kanon Telcoin prototype

This workspace contains an OCaml compiler prototype that checks Kanon source and emits EVM creation bytecode, runtime bytecode, an Ethereum ABI, a map from bytecode to IR nodes, and a provenance manifest.

The source input is a closed `Nat -> Nat` state transition. A fixed counter wrapper supplies persistent state, constructor ownership, ABI dispatch, and checked failure behavior. This is the first executable slice of the [language design](TELCOIN-LANGUAGE-DESIGN.md). Kan-only foundations, Lean 4 parity, full Telcoin execution conformance, and OCaml compilation-speed parity remain open.

The current [validation record](VALIDATION.md) reports a clean build, 73 OCaml checks, 43 local EVM checks, 66 checked-source/IR comparisons, four CLI regression groups, and the first compilation timing calibration.

The existing Kanon checkout was left untouched. The compiler uses 34 committed source and license files from `c4180626123687858ff83408bab801c6f87e3e71`, stored under `third_party/kanon`. [kanon-source.lock.json](kanon-source.lock.json) records SHA-256 hashes. The [Telcoin profile](telcoin-target.json) pins source configuration at `66e0d14a52b042a383b666d4b4da0079ec5b4871`; it does not assert a live network's software version.

**Build and compile.** Required tools are OCaml with Zarith 1.14, Dune 3.24 or newer, and Python 3. `dunecho` is optional. The installed `zxcaml-p1` opam switch supplies the OCaml dependencies in this environment.

```sh
python3 scripts/vendor_kanon.py
dune build bin/main.exe
python3 scripts/kanonc.py examples/counter.kan --bound 3 --out artifacts/counter
```

`dunecho build` provides a compact build report when installed. No package installation or network download is required with the existing toolchain.

The example is actual checked Kanon source:

```text
def step : (state : Nat) -> Nat :=
  fun (state : Nat) => natAdd state 1
```

Select another entry with `--entry NAME`. The output directory can be reused when its artifacts are identical; choose a new directory for changed output. Compilation does not deploy a contract.

The generated files are `creation.hex`, `runtime.hex`, `contract.json`, `abi.json`, `source-map.json`, `source.kan`, and `manifest.json`. Hex files include `0x`. The manifest records source and bytecode hashes, the compiler binary hash, the upstream source lock, the state bound, and the target profile. Source maps use byte offsets and IR node identifiers; surface line information is not available yet.

**Supported semantics.**

| Boundary | Current behavior |
| --- | --- |
| Input | A checked, nonrecursive `Nat -> Nat` definition; native `natAdd`, `natSub`, and `natMul`; natural literals; the state variable; supported strict lets. |
| Initial state | Zero in storage slot 1. |
| Owner | Constructor caller in storage slot 0. |
| `get()` | Returns the current state as one ABI `uint256`. |
| `increment()` | Owner only. Evaluates the compiled transition, stores its result, emits `Incremented(uint256)`, and returns the new state. The name is fixed even if a supplied transition performs another arithmetic operation. |
| Arithmetic | Every executed IR arithmetic intermediate must fit `uint256`. Addition and multiplication overflow revert. Natural subtraction saturates at zero. |
| State bound | A result above `--bound` reverts. The default bound is 1,000,000. |
| ABI checks | Exactly four calldata bytes are required. Unknown selectors, malformed lengths, and nonzero call value revert with empty data. Constructor is also nonpayable. |
| Revert and gas | Failed execution does not persist contract storage or logs. Gas exhaustion is possible, including for terminating source terms. |
| Unsupported source | User axioms, builtin redefinitions, recursion, helper calls, closures, cases, and unsupported runtime layouts fail compilation explicitly. |

The backend is a partial implementation of natural-number computation within EVM resource bounds. It does not turn arbitrary-precision `Nat` into wrapping arithmetic. Its overflow outcomes and state bound are part of the contract wrapper's semantics. The wrapper, eraser, arithmetic lowering, and emitter are currently trusted implementation code with tested examples, not formally verified translations.

Before kernel evaluation, a lexical and syntax preflight checks every declaration, including unused declarations. It admits only bare Nat annotations, explicit single-argument functions, local variables, literals, strict lets, and saturated native arithmetic. It caps numeric lexemes at 78 digits, tokens and expanded arithmetic at 4,096 nodes, nesting at 128, and a conservative estimate of arithmetic values at 16,384 bits. This prevents short repeated-squaring lets from constructing huge integers during checking.

Additional limits are 65,536 source bytes, 20,000 checker budget polls, and 1,024 emitter nodes. The packaged driver imposes a 10-second compiler timeout. The emitter also enforces the 24,576-byte runtime limit and 49,152-byte creation limit. These are prototype restrictions and do not establish the unrestricted expressiveness goal.

Let bindings evaluate their right-hand side once, store the checked value in a fresh memory slot, and reuse it through scoped local references. Unused bindings still evaluate and can revert on overflow. The source preflight retains its conservative expanded-arithmetic limits because it runs before kernel checking. The [shared-let example](examples/shared_let.kan) computes `(state + 1)` once before squaring it.

**Local execution validation.**

```sh
python3 -P tests/compiler_cli.py
python3 -P tests/source_differential.py
python3 -P tests/evm_integration.py
```

The test harness owns a fresh Anvil process bound to loopback, deploys only to that ephemeral process, and shuts it down. It checks bytecode installation, ABI behavior, ownership, storage, logs, arithmetic edge cases, refusals, and rollback. Some boundary fixtures seed state with Anvil's test-only storage RPC. No wallet, public RPC, or live deployment is involved.

The fixed differential corpus runs 25 programs at 66 input states through
the checked source evaluator, the lowered IR evaluator, and EVM execution.
It covers shared and shadowed lets, annotations, unused strict bindings,
natural subtraction, and overflow. Source evaluation bypasses erasure and
IR lowering, so it can expose disagreements in those compiler steps.

```sh
_build/default/bin/main.exe --eval-source step 3 < examples/counter.kan
_build/default/bin/main.exe --eval step 3 < examples/counter.kan
```

Both commands check the source and require a uint256 input. `--eval-source`
returns the pinned kernel's natural-number result, which can exceed uint256.
`--eval` retains checked arithmetic at every IR intermediate. An overflowing
intermediate must fail IR and EVM execution even if the natural final result
fits uint256. The evaluators do not apply the contract wrapper's final state
bound or model gas. The corpus harness gives each evaluator call ten seconds.
The EVM suite gives each compiler call twenty seconds.
Kernel evaluation itself has no budget polling. These are bounded regression
checks, with [recorded evidence](evidence/let-sharing/source-ir.json),
rather than a proof of compiler preservation.

The installed Anvil version predates finalized Prague. Passing these tests supplies baseline EVM evidence for the opcodes used. It does not validate Telcoin's current execution dependencies, custom precompiles, fee distribution, or gas over-reservation policy. The report records this limitation and the actual engine version.

**Performance calibration.**

```sh
python3 scripts/benchmark.py
```

This records full packaged compilation, the raw compiler pipeline, and OCaml bytecode/native baselines. A tiny arithmetic calibration does not satisfy the frozen multi-workload performance contract in the design brief. Performance claims must include source checking and all required artifact work; an isolated emitter time is insufficient.

The [foundation inventory](FOUNDATION-OBLIGATIONS.md) identifies the first dependent-induction obligation and the existing trusted rules. In particular, the reused kernel's opaque built-in `Nat` and native arithmetic are not established Kan derivations. The [conditional bridge](NAT-FRAGMENT-BRIDGE.md) connects a bounded declared-`N` source schema to the initiality model; construction admissibility remains open.

**Lean foundation library.** The root is also a reusable Lake package, pinned
to Lean `v4.33.0-rc1`. Its public entry point is `KanonTelcoin`. The conditional
initiality module is copied from the same exact Kanon commit as the compiler,
with a separate [metatheory source lock](kanon-meta-source.lock.json).

```sh
python3 scripts/verify_metatheory.py
lake build
dune runtest
python3 scripts/check_nat_bridge.py
```

A downstream Lake project can use this checkout without fetching dependencies:

```lean
require «kanon-telcoin» from "/Users/oobi/Documents/kanon-telcoin"
```

Then `import KanonTelcoin` exposes the library. All authored Lean proofs use
term expressions, so the package needs no tactic package or network dependency.
The bridge's initiality hypothesis remains explicit; this package does not
establish the Kan-only construction requirement.

The source fixture and its 37 regression checks are described in
[foundation/README.md](foundation/README.md). They check real Kanon source
from an empty global environment. The cross-language profile check rebuilds
both sides before comparing them. The existing EVM frontend still accepts
only the arithmetic transition fragment described above.

Upstream Kanon retains its bundled MIT and Apache-2.0 notices. No new license has been selected for the authored prototype files.

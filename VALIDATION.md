# Prototype validation, 2026-09-07

The first executable slice is implemented: checked Kanon source passes through the pinned checker and eraser into a restricted arithmetic IR, then a direct EVM emitter. The supplied counter compiles to 162 runtime bytes, with constructor ownership, persistent state, an explicit upper bound, an event, and checked failures. Generated [artifacts](artifacts/counter/manifest.json) correspond to [examples/counter.kan](examples/counter.kan) with bound 3.

| Check | Result |
| --- | --- |
| `dunecho build` | Passed, zero errors and zero warnings. |
| `python3 scripts/vendor_kanon.py` | Verified all 34 copied files against the committed Kanon source lock. |
| `python3 tests/compiler_cli.py` | Four reported groups passed: exact byte-preserving artifact reruns and conflict refusal, source-map instruction boundaries, input-state bounds, and preflight rejection of repeated squaring. |
| `python3 tests/evm_integration.py` | 29 reported checks passed, including 32 arithmetic edge samples. [Machine-readable report](artifacts/evm-validation.json). |
| `panicscan --all --limit=20 lib bin` | Zero findings in the four authored OCaml files. |
| Authored prose and source punctuation | No forbidden em dash characters found. Vendored source was preserved verbatim. |

The EVM checks cover deployment and installed bytecode equality, deterministic emission, owner initialization, nonpayable constructor and calls, public reads, authenticated state changes, exact ABI lengths, malformed selectors, event topics and data, state bounds, arithmetic overflow, natural subtraction, unused strict-let evaluation, and rollback after revert or gas exhaustion. Twelve source variants produce distinct runtime programs. The reference comparison evaluates the restricted arithmetic IR, not the original kernel evaluator; it tests the emitter boundary and does not prove frontend or erasure preservation.

Local execution used Anvil `0.3.0`, commit `5a8bd89`, in its Prague mode with chain ID 2017. Each run owned a temporary process bound to loopback and terminated it afterward. The sandbox initially denied loopback binding; automatic approval allowed the scoped local test process. There was no public network deployment.

That Anvil build predates finalized Prague. These are baseline EVM tests for the opcode subset used, not conformance tests against the pinned Telcoin production execution path. Telcoin-specific precompiles, fees, and gas-reservation behavior remain unverified.

**Timing calibration.** [Raw measurements](artifacts/benchmark.json) record two warmup rounds and seven measured rounds per command, rotated across the four command classes. The toolchain was OCaml 5.2.1, Zarith 1.14, and Python 3.14.7. Installed dependencies and filesystem caches were reused; each measured command used a fresh output directory. The local EVM process had stopped before timing began.

| Command scope | Median | Observed p95 |
| --- | ---: | ---: |
| Full packaged Kanon artifact generation | 124.716 ms | 133.174 ms |
| Raw Kanon compiler, including checking, erasure, EVM emission, and JSON output | 5.499 ms | 5.939 ms |
| OCaml bytecode compiler and Zarith link | 21.047 ms | 21.599 ms |
| OCaml native compiler and Zarith link | 171.658 ms | 206.339 ms |

The full packaged path was approximately 5.93 times the OCaml bytecode baseline and 0.73 times the native baseline on this calibration. The raw pipeline was faster than both. These numbers locate packaging overhead; they do not establish OCaml-speed parity. There is only one tiny workload, the OCaml reference omits the contract ABI/storage wrapper, and this run does not cover cold dependency builds, incremental builds, representative proof workloads, or scaling. With seven samples, the reported p95 is the largest sample.

Three review findings were fixed before the final validation: costly closed expressions now receive syntax/resource checks before kernel evaluation; packaging compares and writes exact source bytes so CRLF reruns remain stable; and reference evaluation validates input bounds even when the program ignores its input. The full execution suite and focused CLI regressions passed after those changes.

**Remaining work.** The [foundation inventory](FOUNDATION-OBLIGATIONS.md) remains an obligation ledger, not a proof. The opaque built-in Nat and native arithmetic in the copied kernel have not been derived from Kan extensions. General checker, erasure, and backend soundness, the Lean expressiveness translation, and full Telcoin conformance remain open. The current source restrictions and resource caps are explicitly narrower than the proposed language.

The prototype's foundation follow-up was a typed bridge from the admitted unary inductive fragment to a justified dependent eliminator, with construction assumptions exposed. The bounded conditional slice is recorded below. The next execution milestone is the same artifact tested under pinned Telcoin execution rules. The first measured performance target is packaging overhead, followed by a representative frozen workload corpus.

**Conditional foundation bridge, 2026-09-07.** The bounded bridge described
in [NAT-FRAGMENT-BRIDGE.md](NAT-FRAGMENT-BRIDGE.md) is implemented as a reusable
root Lake library. Its exact metatheory snapshot uses the compiler's existing
Kanon commit. No vendored compiler files changed.

| Check | Result |
| --- | --- |
| `leancho --warn` | Library and independent client tests passed with zero errors, unfinished proofs, and warnings. |
| Separate Lake project using `require` and `import KanonTelcoin` | Passed with zero errors, unfinished proofs, and warnings. |
| `dunecho build` and `dunecho test` | Passed with zero errors and warnings; the source adapter harness reports 37 checks. |
| `python3 tests/compiler_cli.py` | All four existing regression groups passed. |
| `python3 scripts/check_nat_bridge.py` | Freshly built OCaml and Lean profiles agree; both copied source snapshots verify. |
| `lake env lean test/BridgeAxioms.lean` | Only `propext` and `Quot.sound` appear where used; no unfinished-proof or new axiom. Initiality remains an explicit parameter. |
| `panicscan --all --limit=20 lib bin` | Zero findings across five authored OCaml files. |

The independent Lean client exercises substitution into a motive depending
on both the source scrutinee and an outer variable. It also computes a
dependent `Fin` witness by structural source recursion without assuming
initiality. This concrete external Lean model is a regression fixture, not
an object-language natural-number construction.

Review found and fixed stale-build reuse in the profile harness and ignored
application annotation gaps in the adapter. The adapter now rejects
out-of-scope, ill-typed, and mismatched application domains, including
payloads ignored by the pinned checker. Its fixture checks dependent case
and recursion from an empty global environment, without builtin natural
arithmetic.

These are conditional bridge and adapter checks. Full Kan construction
admissibility, general compiler correctness, Telcoin execution conformance,
and the performance gates remain open. The earlier EVM and timing results
above remain the prototype's prior records.

**Checked source differential validation, 2026-09-07.** The new
`--eval-source ENTRY STATE` path checks the source and a core application,
then evaluates it with the pinned kernel. It shares preflight and source
checking with compilation, but bypasses erasure, IR lowering, and the IR
evaluator. Existing compilation and `--eval` behavior remain covered by the
CLI regressions. No vendored source or Lean proof changed.

| Check | Result |
| --- | --- |
| `dune build bin/main.exe` | Passed without diagnostics. |
| `dune runtest` | Passed, including all 37 foundation adapter checks. |
| `python3 -P tests/compiler_cli.py` | All four regression groups passed. |
| `python3 -P tests/source_differential.py` | 20 programs, 53 source/IR samples, 13 rejected input cases, and a nondefault entry check passed. |
| `python3 -P tests/evm_integration.py` | All 37 reported groups passed, including the same 53 differential samples through local EVM execution. |
| `panicscan --all --limit=20 lib bin` | Zero findings across five authored OCaml files. |
| Independent static review and `git diff --check` | Completed; the identified EVM failure-reporting issue was fixed. |

The [source/IR report](evidence/source-differential/source-ir.json) records
the compiler binary, authored compiler source, upstream lock, and corpus
hashes. The [EVM report](evidence/source-differential/evm.json) records the
same compiler and corpus hashes, the local engine version, observed source
and IR outcomes, EVM results, storage, and log counts. Forty samples return
matching values. Thirteen samples compute a natural result but require
checked intermediate overflow and EVM revert. This includes discarded lets
and expressions whose natural final result fits uint256.

The EVM suite requires a revert for rejected calls; out-of-gas errors no
longer satisfy that check. Separate low-gas coverage still verifies rollback.
All deployments used an owned temporary loopback Anvil process. Its
Prague-mode results remain baseline EVM evidence, with the engine limitations
described above. Pinned Telcoin production execution remains the next
execution milestone: the local target commit and its six recorded source
hashes were verified, but a matching execution runner is not installed.

The oracle retains uint256 input bounds, frontend resource limits, and an
external timeout in the harness. Its natural result is unrestricted by the EVM
word limit. The corpus harness gives each evaluator call ten seconds. The EVM
suite gives each compiler call twenty seconds. Kernel evaluation has no budget polling, and the
oracle does not model the final wrapper bound or gas. This finite corpus
tests the source-to-IR boundary; it does not prove general checker, erasure,
or backend correctness, Kan-only foundations, or Telcoin conformance.

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

**Shared strict lets, 2026-09-07.** The contract IR now preserves `Let` and
scoped `Local` nodes. Lowering no longer substitutes a binding into every use
or adds artificial multiplication and addition to sequence its evaluation.
Both the IR evaluator and EVM execute each binding's right-hand side once,
including unused bindings that must fail on intermediate overflow. EVM
bindings use fresh memory slots, disjoint from arithmetic scratch and wrapper
output. Invalid local indices return explicit errors.

| Check | Result |
| --- | --- |
| `dunecho build` | Passed, zero errors and warnings. |
| `dune runtest --force` | All 36 IR/lowering/emitter checks and 37 existing foundation checks passed. |
| `python3 -P scripts/vendor_kanon.py` | All 34 pinned source files verified. |
| `python3 -P tests/compiler_cli.py` | All four regression groups passed. |
| `python3 -P tests/source_differential.py` | 25 programs, 66 source/IR samples, 13 refusals, and the nondefault entry check passed. |
| `python3 -P tests/evm_integration.py` | All 43 groups passed, including the same 66 corpus samples and two sharing-comparison samples. |
| `panicscan --all --limit=20 lib bin` | Zero findings across five authored OCaml files. |
| Independent compiler and test review | Seven defects were found and fixed. They are listed below this table. |
| `git diff --check` | Passed. |

The review fixed these defects:

- The emitter's local-index guard used an if/else-if chain instead of a `match ()` guard chain.
- The IR test recorded an emitter pass for any successful compilation, without reading the artifact.
- No check exercised the 1,024-node or the depth-256 emitter limit.
- A corpus comment claimed the expanded doubling chain exceeds the 1,024-node emitter limit. It is 511 nodes.
- The authored-source lint never ran in the EVM harness, so a new `lib/*.ml` file could go unhashed.
- The EVM sharing case compiled an inline copy of the shared example, not the committed file.
- This record said eight levels of shared doubling. The corpus builds seven doubling levels.

The [source/IR report](evidence/let-sharing/source-ir.json) and
[EVM report](evidence/let-sharing/evm.json) record the tested compiler binary,
all nine compiler source/build-file hashes, the source lock, and corpus hash.
The EVM report also hashes its harness. Earlier checkpoint reports remain in
`evidence/source-differential`. The final run used Python 3.14.7 after the
validation shell initially selected an older system interpreter that lacked
`-P`; that attempt stopped after the successful OCaml checks.

The new corpus cases exercise seven doubling levels over one shared base
binding, nested RHS shadowing, restoration of an outer local after a sibling
expression, and unused strict overflow inside and outside a RHS. Direct IR
tests also reject negative indices, escaping locals, and a binding used in its
own RHS. The source preflight's expanded-arithmetic, nesting, and bit limits
remain unchanged, as do the checker and emitter limits. Direct IR tests now
pin both emitter limits. A nest of 257 lets fails the depth limit, a nest of
256 lets is emitted, a 1,025-node expression fails the node limit, and a
1,023-node expression is emitted.

At input state 3, the shared [example](examples/shared_let.kan) and an
explicitly repeated `(state + 1)` expression both return and store 16 with
one event. The shared variant emits one `ADD` and one `MUL`; the repeated
variant emits two `ADD` operations and one `MUL`.

| Local execution measurement | Shared binding | Explicit repetition |
| --- | ---: | ---: |
| Runtime bytes | 246 | 277 |
| Transaction gas used | 29,557 | 29,718 |

These measurements use identical seeded storage and calls under the owned
temporary Anvil process. They demonstrate this expression's reduced bytecode
and gas use, without establishing a general performance bound. No compilation
latency measurement was rerun. The existing limits on Kan-only foundations,
Lean parity, compiler proofs, and pinned Telcoin execution conformance still
apply.

**Packaging startup, 2026-09-08.** Packaging now calls the source-snapshot
verifier in its own process instead of launching another Python interpreter.
Each invocation still checks the exact pin, file inventory, and every source
hash before compilation. Absolute-path loading supports `-P` and
`PYTHONSAFEPATH=1` from unrelated working directories. The artifact manifest
adds `source_verifier_sha256`, and the existing four-way calibration also
records that hash.

| Check | Result |
| --- | --- |
| `dunecho build` on a fresh workspace copy | Passed, zero errors and warnings. |
| `python3 -P scripts/vendor_kanon.py` | All 34 pinned files verified. |
| `python3 -P tests/compiler_cli.py` | All four existing regression groups passed. |
| `python3 -P tests/packaging.py` | All fourteen new regression groups passed. |
| Paired packaging calibration, two warmups and 15 measured runs per version per example | All 102 compilations and 51 artifact comparisons passed. |
| Existing four-way calibration with zero warmups and one run | Passed as a CLI/provenance smoke check; no timing claim uses that sample. |
| Independent review of packaging regressions and paired calibration | Seven defects found; six fixed in this slice, and the seventh fixed by regenerating the calibration receipt. |
| `git diff --check` | Passed. |

The review fixed these defects:

- A source lock that is not an object of string hashes now fails with the
  documented exit code instead of a traceback.
- A source verifier that does not compile now fails with the documented exit
  code instead of a traceback.
- Rejection checks now require the tool diagnostic prefix and no traceback.
- The safe-path group now plants a real shadowing module beside the scripts.
- Concurrent packagers into one directory now serialise on an exclusive marker.
- Five assertions now name the defect instead of passing child output alone.
- The calibration receipt no longer records a report path outside the
  repository.

The new regressions check exactly seven artifacts, complete provenance hashes,
CRLF source bytes, deterministic reruns, refusal to overwrite conflicting
output, a refused corrupt source verifier, and one consistent artifact set from
two concurrent packagers. A shadowing module beside the scripts is loaded
without a safe path and ignored under `-P` and `PYTHONSAFEPATH=1`. Eight
isolated mutations cover changed, missing, and extra snapshot files, an
incorrect pin, malformed JSON, a missing pin field, and two lock shapes that
are not an object of string hashes. Both the
standalone verifier and the packager reject each mutation. Existing artifacts
stay byte-identical, and a fresh output directory is never published on those
failures. Restoring the snapshot reproduces the original artifact bytes.

The [paired report](evidence/packaging/paired.json) compares packaging scripts
from commit `c8b0ea51469f323577310c50c17963ea9bd70185` with the new scripts.
Both versions use identical copied compiler binaries, compiler sources,
upstream snapshots, target profiles, and example inputs. Timing includes
process startup, verification, source checking, emission, and all artifact
writes into fresh output directories. Setup and artifact comparisons run
outside the timed interval. Version order alternates and example order
rotates each round.

| Example | Previous median | New median | Median paired new/previous ratio |
| --- | ---: | ---: | ---: |
| `counter.kan` | 155.067 ms | 87.649 ms | 0.548 |
| `step_two.kan` | 147.488 ms | 84.349 ms | 0.551 |
| `shared_let.kan` | 156.426 ms | 90.905 ms | 0.575 |

Median paired elapsed time fell by 42.5% to 45.2% across these examples. The
ratio of medians is a different statistic, also recorded in the report.
All six non-manifest artifacts match byte-for-byte across versions. Manifests
match after removing only the separately verified packager and verifier
hashes. All seven files remain identical across repetitions of each version.

This is a local calibration with warm filesystem caches and installed
dependencies, not a performance gate. The host's one-minute load average rose
from 19.82 to 24.92 during the run. Two of the 45 measured pairs were slower
after the change, and the report retains every sample and nearest-rank p95.
These three small arithmetic examples do not establish representative workload
performance, cold or incremental build speed, or OCaml compilation parity.

The compiler and emitter sources are unchanged in this increment. Their nine
source/build-file hashes still match the existing source/IR and EVM evidence;
those execution suites were not rerun for this packaging-only change. The
[validation receipt](evidence/packaging/validation.json) records current test
and script hashes, captured check results, and that reuse check. Pinned Telcoin
execution and the foundation obligations remain open.

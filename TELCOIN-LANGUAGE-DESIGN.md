# Kan-based smart contract language for Telcoin

Design brief, 2026-09-07. The user accepted the recommended implementation direction and authorized proceeding. The first prototype reuses a committed Kanon snapshot and adds an OCaml EVM backend. The acceptance criteria remain goals; this document does not claim that the four requirements have been achieved.

The requested language has Kan extensions as its only primitives, targets Telcoin Network, compiles at least as fast as OCaml, and matches or exceeds Lean 4 in type safety, logical strength, and expressiveness. These requirements remain the goal. Reusing Kanon is the selected implementation direction. The strict primitive requirement remains an open foundation obligation; proceeding with a prototype does not certify or relax it.

| Requirement | Assessment | Evidence needed for completion |
| --- | --- | --- |
| Only Kan primitives | The central research risk. Two constructor names alone do not establish this property. | Complete trusted rule inventory and derivations for every claimed construction. |
| Telcoin target | A concrete EVM backend engineering task. | Reproducible bytecode and ABI artifacts executed under pinned Telcoin rules. |
| At least OCaml compilation speed | An empirical target requiring a specified comparator and workload. | End-to-end measurements against both `ocamlc` and `ocamlopt`, with all mandatory compiler work included. |
| At least Lean 4 types and expressiveness | A substantial metatheory and implementation obligation. | A general Lean-to-language translation, soundness evidence, and compiler correctness for the executable fragment. |

**Recommended implementation direction.** Reuse a pinned Kanon kernel if its foundations survive the stricter audit, implement the compiler in OCaml, and add a Telcoin EVM backend. A separate language can use the same architecture without inheriting Kanon's surface syntax or name. Implementation in OCaml is a reuse decision, not evidence of compilation speed.

Read-only inspection found an existing Kanon checkout at `/Users/oobi/Documents/kanon`, HEAD `c4180626123687858ff83408bab801c6f87e3e71`, with staged work. Findings here describe the current files, including those staged changes. Its implemented kernel and WasmGC path offer reusable machinery, but there is no EVM backend. The [foundation audit](/Users/oobi/Documents/kanon/dev/FOUNDATION-AUDIT.md:7) leaves the Kan derivation of inductive behavior unestablished. Existing work must be evaluated at an exact snapshot; a successful earlier gate is not a verification of the current tree. No build or test was run during this inspection.

The current [term syntax](/Users/oobi/Documents/kanon/lib/term.ml:46) has 13 constructors, of which two are counted as type formers. Additional framework rules and an opaque builtin `Nat` are part of the actual trust inventory. [Shape checking](/Users/oobi/Documents/kanon/lib/rules.ml:1425) implements `SPi`, `SColl`, and `SMu`, while `SPar` and `SNu` remain deferred. Nested inductives, universe polymorphism, computational quotients, and general parity arguments remain open. The staged Lean semantics work also [limits its construction claims](/Users/oobi/Documents/kanon/dev/INDEXED-CONSTRUCTION.md:11); an external model using Lean's primitives does not establish a derivation in the proposed kernel.

**Foundation.** Start from an explicitly specified indexed setting with contexts, substitutions, universes, and reindexing. For a context projection `p : Gamma.A -> Gamma`, the desired adjunction is:

```text
Sigma_p  ⊣  p*  ⊣  Pi_p

Sigma_p is represented by an appropriate dependent Lan construction.
Pi_p    is represented by an appropriate dependent Ran construction.
```

This is a semantic starting point. It requires a precise account of existence, universe levels, substitution stability, and computation. Ordinary Kan extensions are adjoints to precomposition when they exist; that universal property does not by itself constitute a dependent type checker. [Riehl, Category Theory in Context, chapter 6](https://emilyriehl.github.io/files/context.pdf)

The foundation must enumerate all trusted syntax and rules, including introduction, elimination, conversion, equality, universes, literals, and shape admissibility. Calling an inductive former `Lan SMu` does not derive its induction principle. Calling quotient construction a coequalizer does not derive the required equality and computation rules. Every accelerator must have a reference meaning and a correctness obligation.

If the requirement means “Lan and Ran are the only type formers,” explicit ambient rules can be listed and audited. This matches the direction of the existing Kanon design, but still requires a justification for each shape. If the requirement means “every additional logical and computational rule must be derived from Kan extensions,” reuse of that design remains conditional. This brief does not silently substitute the weaker interpretation.

Finite products and coproducts alone are insufficient evidence for induction. As a mathematical counterexample, finite sets support finite diagram Kan extensions but have no natural-number object. A finite grammar containing recursive or infinite shapes can escape that example, but must justify its added initiality or recursion assumptions.

The first foundation deliverable is a rule specification with derivations of dependent functions, dependent pairs, `Nat` with dependent induction and computation, equality transport, and indexed vectors. Audit substitution under binders and the stability of these constructions under reindexing. A derivation that assumes the same inductive principle it claims to construct fails this milestone.

**Lean 4 parity.** Pin an exact Lean version and state the chosen axiom policy. Cover dependent functions, universe polymorphism, impredicative `Prop`, proof irrelevance, inductive families, mutual and nested induction, quotient elimination, and the relevant computation and eta rules. Lean's kernel behavior is the comparator; familiar surface syntax alone cannot establish parity. [Lean type system](https://lean-lang.org/doc/reference/latest/The-Type-System/), [Lean universes](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/), [Lean inductive types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)

Use separate evidence for three claims:

1. Expressiveness: translate the pinned Lean kernel calculus into the language while preserving typing, substitution, universe constraints, and computation under the stated encoding. Preserve observable distinctions to exclude a vacuous translation.
2. Logical safety: justify the new calculus and checker by a semantic soundness argument or an appropriate interpretation into an accepted foundation. Track all axioms. An inconsistent system would pass many positive examples, so positive examples cannot establish safety.
3. Executable correctness: prove or otherwise explicitly qualify the correspondence between checked source computations and emitted EVM behavior. Kernel correctness does not establish backend correctness.

Differential tests should include both accepted and rejected terms, malformed recursors, invalid universe constraints, invalid positivity, escaping variables, and erased-proof misuse. These are regression evidence, not a substitute for the general arguments. Tactics, inference, modules, diagnostics, and library support are separate usability work; logical parity does not imply automatic mathlib source compatibility.

Support full mathematical specifications while requiring contract entry points to have computational content. Lean itself permits noncomputable definitions, and choice-generated runtime data cannot simply become executable code. Proof erasure must preserve every dependency that affects runtime computation. [Lean axioms and computation](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/)

**Telcoin compilation.** Telcoin's official repository describes Ethereum-compatible EVM execution. The native contract artifact is EVM bytecode. The existing WasmGC output needs a different backend to become a Telcoin contract. [Telcoin Network repository](https://github.com/Telcoin-Association/telcoin-network)

The proposed local compatibility profile pins Telcoin source commit `66e0d14a52b042a383b666d4b4da0079ec5b4871`. Its checked-in mainnet and testnet genesis configurations enable Shanghai, Cancun, and Prague from timestamp zero. This is source configuration evidence, not a live-network verification. Record the genesis hash, hardfork schedule, execution dependency revisions, precompiles, and compiler options in the target manifest. Verify the selected deployment network independently before publishing an artifact. [Pinned mainnet genesis](https://github.com/Telcoin-Association/telcoin-network/blob/66e0d14a52b042a383b666d4b4da0079ec5b4871/chain-configs/mainnet/genesis.yaml)

The pinned lockfile selects Reth `1.11.3` at `d6324d63e27ef6b7c49cdc9b1977c1b808234c7b` and revm `34.0.0`. The pinned official contract submodule uses Solidity `0.8.35` with `evm_version = "prague"`, a suitable initial interoperability reference. [Execution dependencies](https://github.com/Telcoin-Association/telcoin-network/blob/66e0d14a52b042a383b666d4b4da0079ec5b4871/Cargo.lock), [contract toolchain](https://github.com/Telcoin-Association/tn-contracts/blob/0fb6b01f289076e2ae13c33048ff1e581807dfa1/foundry.toml)

Telcoin's execution factory adds TEL issuance and BLS precompiles, and its compatibility documentation describes modified fee behavior. Use the production execution path for final conformance. A generic EVM runner can test standard opcode behavior but does not establish compatibility with these extensions. The official local development network is a later execution gate; it was not started during this research. [Execution factory](https://github.com/Telcoin-Association/telcoin-network/blob/66e0d14a52b042a383b666d4b4da0079ec5b4871/crates/tn-reth/src/evm/factory.rs), [compatibility rules](https://github.com/Telcoin-Association/telcoin-network/blob/66e0d14a52b042a383b666d4b4da0079ec5b4871/docs/src/evm-compatibility.md)

```text
Surface declarations and proofs
  -> elaboration
  -> independently checked Kan core
  -> proof erasure and runtime representation selection
  -> typed contract IR
  -> direct EVM emission
  -> creation bytecode + runtime bytecode + ABI + source map + manifest
```

The first backend can use Yul through a pinned `solc` to shorten the route to executable evidence. Solidity supports standalone Yul compilation for EVM. Retain that route as a differential reference if useful. The release architecture should evaluate direct EVM emission to control compilation cost; neither route is assumed fast before measurement. Include `solc` time whenever the artifact depends on it. [Official Yul documentation](https://docs.soliditylang.org/en/latest/yul.html)

Kanon's existing [driver seam](/Users/oobi/Documents/kanon/bin/kanon.ml:86) goes from checked declarations through erasure into Wasm emission. Its [erased representation](/Users/oobi/Documents/kanon/lib/eterm.ml:17) is a useful starting point, but reference layouts and `RI31` representations require redesign for EVM. Backend reuse must preserve the semantics of those values rather than mechanically remap instructions.

The contract IR owns 256-bit words, addresses, memory, persistent storage, ABI dispatch, events, calls, and revert behavior. This machine vocabulary belongs to the target semantics; it must not create untracked logical assumptions. Source-level effects can be represented as derived typed descriptions with an explicitly specified interpreter into EVM operations. If the strict primitive requirement also covers effect semantics, that encoding is another foundation obligation.

Define natural numbers and machine words separately. Natural arithmetic must not silently wrap at 256 bits. Word operations must state whether they wrap, fail, or require checked preconditions. Out-of-gas and revert are modeled execution outcomes. Source termination does not guarantee execution within a transaction's gas allowance.

Keep ABI boundaries explicit: external callers supply bytes, not trusted proofs. Validate decoded values and dynamically establish necessary refinements. Prove or test the chosen encoding and decoding behavior against the standard, including rejection of malformed inputs. [Contract ABI specification](https://docs.soliditylang.org/en/latest/abi-spec.html)

Specify storage layouts and schema versions as artifact data. Model external calls with explicit success and failure, value transfer, and reentrancy. A contract's proved invariant must state its assumptions about callers and other contracts. Capabilities or indexed effects are promising ways to enforce access policies, but they also need their own preservation argument.

The first stateful example should be an owner-controlled bounded counter: `get` and `increment`, constructor-set owner, explicit overflow failure, and an event on success. Check authorized execution, unauthorized calls, malformed calldata, boundary arithmetic, persistent state, revert atomicity, and low-gas execution against source semantics. Add a second example with an external call before claiming support for cross-contract reasoning.

**Compilation speed.** “At least as fast as OCaml” needs a workload correspondence and a latency definition. OCaml's bytecode and native compilers produce different artifacts; measuring against only the slower comparator would not establish an unqualified OCaml-speed claim. [OCaml bytecode compiler](https://ocaml.org/manual/5.4/comp.html), [OCaml native compiler](https://ocaml.org/manual/5.5/native.html)

Proposed benchmark contract, subject to the intended meaning of the requirement:

| Corpus | Measurement | Proposed gate |
| --- | --- | --- |
| Equivalent shared computational programs | Complete clean compilation on the same machine, separately versus pinned `ocamlc` and `ocamlopt` | Median latency ratio at most 1.0 for every named pair against each comparator. |
| The same programs after a prescribed edit | Complete incremental compilation with declared cache state | The same ratio rule, reported separately from clean builds. |
| Dependent and proof-heavy programs | Elaboration, proof checking, and compilation, with a pinned Lean comparison where meaningful | Publish distributions and scaling. This corpus has no automatic equivalent OCaml baseline. |
| Representative stateful contracts | Source to deployable artifact, including every external compiler | Publish latency, peak memory, bytecode size, and execution gas. |

Use a fixed corpus with small, medium, and large modules; recursive data; polymorphism; cross-module dependencies; and invalid programs. Freeze source hashes, command lines, tool versions, machine details, parallelism, and benchmark procedure. Pair the order of runs, include warmups, report medians and tails, and rerun noisy measurements. Do not normalize solely by source lines or select only favorable examples.

Include parsing, elaboration, conversion, required proof construction, proof checking, erasure, optimization, emission, and linking or assembly in the advertised total. Report optional proof search separately, but include it when a normal build actually requires it. Imported checked artifacts need a sound cache trust policy. A warm proof cache cannot substitute for cold checking without disclosure.

Use sharing, lazy conversion, type-directed equality, checked module interfaces, dependency-aware caching, and separate compilation as candidate implementation techniques. Preserve complete checking on the accepted fragment. A compiler timeout must return an explicit incomplete result, never unchecked success. A fixed timeout that rejects otherwise supported Lean terms also qualifies the expressiveness claim.

There is no demonstrated universal OCaml-speed bound for this proposed language. The benchmark contract makes a practical performance claim falsifiable; it does not prove such a bound for arbitrary dependent programs.

Kanon's current [Stage L record](/Users/oobi/Documents/kanon/dev/M1-BUILD-LOG.md:1775) reports outstanding timing and agreement gates. Its existing normalized timing ratio uses a tot kernel-suite denominator, not equivalent OCaml compilation. Those historical numbers are not evidence that this new performance requirement passes.

**Build sequence and completion gates.**

1. Foundation checkpoint: publish the complete rule inventory and derive the first dependent induction fragment. Record every additional assumption. If the derivation fails the selected primitive policy, revise the calculus before expanding backend work.
2. Executable checkpoint: freeze a kernel snapshot and a Telcoin target profile, then compile a pure function and the bounded counter through a minimal EVM path. Ship bytecode, ABI, source map, target manifest, and reproducible local execution fixtures. Reject unsupported features explicitly.
3. Contract semantics checkpoint: cover words, storage, ABI, effects, external calls, erasure, and failure outcomes. Add source-versus-EVM differential testing. Record the trusted compiler and VM components and unresolved correctness obligations.
4. Parity checkpoint: complete the pinned Lean calculus translation and soundness work, expand the differential corpus, and implement the missing inductive, universe, and quotient behavior. Treat coinduction as an optional extension until baseline parity is established.
5. Performance checkpoint: run the frozen clean and incremental suites, profile failures, and make backend and representation choices from measured results. Neither successful execution nor a tiny-kernel benchmark satisfies this checkpoint alone.

The first useful outcome is an audited dependent induction fragment plus one locally executed Telcoin-compatible stateful contract. That is an initial milestone, not fulfillment of the complete language specification.

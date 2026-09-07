# Conditional natural-number fragment bridge

This milestone connects a bounded Kanon source schema to an external Lean
model. The family is declared as `N`, with `zero : N` and `succ : N -> N`.
It is distinct from the compiler's opaque builtin `Nat` and its native
arithmetic. Initiality remains a premise, and Kan construction admissibility
remains unresolved.

The exact compiler snapshot is recorded in `kanon-source.lock.json`. The
conditional `KanonMeta.Initiality` module comes from that same commit and is
recorded separately in `kanon-meta-source.lock.json`. Neither snapshot follows
the sibling Kanon checkout's working tree.

The source fixture is [nat-fragment.kanon](foundation/fixtures/nat-fragment.kanon).
It is checked from an empty global environment. Its varying `Fiber` returns
`N` at zero and `prod (N, N)` at a successor. Both direct dependent case
analysis and a guarded recursive function return values in this family.

The adapter validates the checked source structure before publishing a
profile. The profile identifies a closed, unindexed `SMu` family, the two
constructor addresses, the successor field and its quantity, the motive's
self binder, and the predecessor-only successor branch. The successor branch
receives no implicit induction hypothesis. The recursive source function
explicitly calls itself on that predecessor.

The Lean model uses the Unit-indexed polynomial `1 + X`. Its scoped source
terms represent variables, zero, and successor. Dependent case and recursion
are represented by a fixed schema with typed motive and branch parameters.
This bounds the claim: arbitrary Kanon branch expressions and general
elaboration are outside this module.

Formal local contexts contain only `N`-valued variables. The motive and
branch operations `P`, `z`, and `s` are typed semantic parameters, rather than
entries in a formalization of the compiler's entire mixed context. The
`guarded_realizes_elim` theorem compares structural evaluation with the
displayed eliminator on closed constructor inputs (`SourceTerm 0`). Open
case and recursion code have reindexing theorems for the specified semantic
interpretation; those are not general OCaml evaluator substitution theorems.

The public theorem groups are:

| API | Claim |
| --- | --- |
| `toSum_fromSum`, `fromSum_toSum` | The polynomial layer corresponds to `1 + X`. |
| `typed_substitution`, `motive_reindexing` | Interpretation commutes with the represented typed substitutions, including dependent motives. |
| `case_beta_preservation` | Both represented source case reductions preserve interpretation. |
| `guarded_realizes_elim` | Structural evaluation of closed constructor terms agrees with the conditional displayed eliminator. |
| `case_reindexing`, `induction_reindexing` | Dependent result transport agrees with reindexing the semantic parameters. |
| `zero_ne_succ_zero` | Every model satisfying the initiality premise separates zero from successor zero. |

The two source representations are connected by an executable agreement
check, `python3 scripts/check_nat_bridge.py`. The OCaml side accepts and
inspects the source fixture, while the Lean side reports the modeled
profile. This is regression evidence for the adapter boundary. Equality of
profiles is not a proof that the OCaml checker or elaborator implements the
Lean judgments for every input.

The remaining trust boundary is explicit:

| Item | Status |
| --- | --- |
| Existence of the carrier and its initial algebra | Supplied by the `Initial` premise. |
| Induction derived from that premise | External Lean metatheory, with dependent pairs, equality transport, and function extensionality. |
| Kanon's object-level Kan construction | Unresolved, including existence, preservation, substitution coherence, and computational equality. |
| Source case and guarded recursive schema | Bounded to the represented fragment and its typed parameters. |
| Opaque builtin `Nat`, literals, and arithmetic accelerators | Not identified with `N` by this bridge. |
| EVM compilation of inductive or recursive source | Unsupported by the existing compiler frontend. |
| General checker, erasure, or backend correctness | Unproved. |

All bridge computation theorems are propositional equalities in Lean. They
do not add judgmental reduction rules to Kanon. The model uses Type 0
motives; higher universes, general indexed inductives, and full Lean parity
remain later obligations.

The [axiom audit](evidence/nat-fragment/axioms.txt) records `propext` and
`Quot.sound` where used by these proofs, with no `sorryAx` or added axiom.
The initiality premise is a theorem argument, so it does not appear in that
printed axiom list. The [profile record](evidence/nat-fragment/profile.json)
contains the checked fixture hash and the common source/model profile.

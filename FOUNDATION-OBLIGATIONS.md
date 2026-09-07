# Foundation obligations for the Telcoin language

Initial inventory, 2026-09-07. The Kan-only requirement remains unchanged. This records existing trusted behavior and the work needed to derive it; it does not certify that behavior as Kan-derived.

**Source boundary.** Compiler evidence below comes from `git show c4180626123687858ff83408bab801c6f87e3e71:<path>` in `/Users/oobi/Documents/kanon`. That commit was still HEAD during inspection. The checkout contains staged changes, so its working files are not an interchangeable source pin. Source references identify paths and symbols at this commit; clickable links open the current checkout. No build, proof check, or runtime test was run for this inventory.

The committed [foundation audit](/Users/oobi/Documents/kanon/dev/FOUNDATION-AUDIT.md) describes a conditional initiality-to-induction bridge. Its current staged revision additionally links staged `dev/INITIAL-CHAIN.md` and `dev/INDEXED-CONSTRUCTION.md`. Those documents and their construction modules are absent from the pinned HEAD. They report later external Lean constructions and earlier validation, not new validation performed here. The committed metatheory toolchain is `leanprover/lean4:v4.33.0-rc1`.

**Initial trusted-rule inventory.** This is a map of the relevant implementation boundary, not yet an exhaustive formal inference-rule specification.

| Boundary | Committed source evidence | Derivation obligation |
| --- | --- | --- |
| Terms and binders | [lib/term.ml](/Users/oobi/Documents/kanon/lib/term.ml), `t`, has 13 syntax constructors: variables, universes, Lan/Ran, four introduction/elimination schemas, let, annotation, globals, literals, and Auto. | Specify well-scoped contexts, substitutions, typing, and the meaning of each schema. Counting two former names establishes no derivation. Auto is declared syntax but refused by the checker. |
| Shape admission | [lib/shape.ml](/Users/oobi/Documents/kanon/lib/shape.ml), `t`; [lib/rules.ml](/Users/oobi/Documents/kanon/lib/rules.ml), `rules`. SPi, SColl, and left SMu are admitted; SPar, SNu, and right SMu are refused. | Give each admitted shape a category, diagram, admissibility judgment, universal property, and computational interpretation. SMu's family name and indices do not supply initiality. |
| Universes | `lib/level.ml`, `succ`, `max`; `lib/check.ml`, `infer_node`; `lib/rules.ml`, `imax`, `spi_lan_lvl`, `spi_ran_lvl`. Closed integer levels and explicit formation calculations are implemented. | Justify stratification, the impredicative Prop rule, representation bounds, and substitution stability. Universe variables and their constraints are not provided by integer levels. |
| Dependent functions and pairs | `lib/rules.ml`, `spi_pack`, its formation, introduction, elimination, beta, and both eta operations. | Derive the operations and typed equations from the proposed dependent Kan construction. A hand-written rule pack is the implementation to justify. |
| Finite collections | `lib/rules.ml`, `coll_pack`, implements finite sums/products, constructor/projection beta, and product eta. | Derive the corresponding finite Kan constructions and their equations, including empty collections. No general inductive existence result follows from this fragment. |
| Conversion and propositions | [lib/conv.ml](/Users/oobi/Documents/kanon/lib/conv.ml), `conv`, `is_prop`, `eta_step`; `lib/rules.ml`, `mu_large`, `mu_subsingleton`. | Account for definitional proof irrelevance, equality checking, and the restricted large-elimination policy. These are trusted rules until justified. |
| Family admission | [lib/positivity.ml](/Users/oobi/Documents/kanon/lib/positivity.ml), `family`, `positive`; `lib/check.ml`, `declare_family`, `define_ctors`. | Connect constructor tables, universe checks, result indices, and positivity to a typed polynomial interpretation. The current policy defers nested inductives. |
| Dependent case analysis | `lib/rules.ml`, `mu_motive_of`, `mu_branch`, `mu_elim_elim`, `mu_beta`. Branches bind constructor fields; beta directly evaluates the selected branch. Both mu eta flags are false. | Derive dependent elimination and justify its operational equations. Propositional uniqueness and judgmental computation are distinct obligations. |
| Structural recursion | [lib/totality.ml](/Users/oobi/Documents/kanon/lib/totality.ml), `guard_group`; [lib/order.ml](/Users/oobi/Documents/kanon/lib/order.ml), `certify`, `translate`; evaluator unfolding. | Prove that accepted recursive definitions correspond to the derived fold/induction principle. A decreasing-call certificate alone is not a Kan derivation. |
| Built-in naturals and arithmetic | [lib/global.ml](/Users/oobi/Documents/kanon/lib/global.ml:124), `initial`, seeds opaque `Nat : Type 0` as an Axiom and five Prim entries. [lib/prim.ml](/Users/oobi/Documents/kanon/lib/prim.ml), `catalog`, `apply`, implements add, truncated subtraction, multiplication, equality, and comparison. | Distinguish this opaque Nat from a declared unary SMu family. Derive a reference natural-number representation and operations, then prove accelerator agreement for their full domain. The initial Nat entry is omitted from ordinary user-axiom disclosure by design. |
| Usage and erasure | `lib/quantity.ml`; `lib/check.ml`, `readable`, `close`; `lib/erase.ml`. Quantities govern erased, single-use, and unrestricted variables. | Establish typed substitution, usage preservation, and erasure correctness. These rules are not discharged by a backend execution fixture. |
| Globals and postulates | `lib/global.ml`, `Def`, `Axiom`, `Prim`; `lib/check.ml`, `check_decl`. | State the axiom policy and trust boundary. An empty user-axiom report does not enumerate the built-in rules or native accelerators. |

The committed [meta/KanonMeta/Syntax.lean](/Users/oobi/Documents/kanon/meta/KanonMeta/Syntax.lean) mirrors only SPi/SColl and excludes SMu and constructor addresses. Its raw substitution lemmas therefore cannot establish typed SMu substitution or correctness of the current mu checker.

**First natural-number derivation obligation.** Use a fresh family `N`, distinct from built-in opaque `Nat`, with one nullary constructor `zero` and one unary constructor `succ : N -> N`. Its candidate polynomial is `F(X) = 1 + X`.

The first complete claim must construct `N` and its constructors using an explicitly admitted Kan construction, without assuming initiality, an N recursor, or the compiler's mu induction rule. It must then derive, for a motive `P : N -> Type 0`:

```text
z : P zero
s : (n : N) -> P n -> P (succ n)
ind(P, z, s) : (n : N) -> P n

ind(P, z, s, zero) = z
ind(P, z, s, succ n) = s n (ind(P, z, s, n))
```

This deliberately bounded first milestone uses Type 0 motives. Full Lean parity separately requires the appropriate higher-universe and Prop cases. State whether each equation is propositional or judgmental. The implementation's beta reduction needs a semantic preservation theorem, and the proposed object calculus needs its own justified computational equality rules; propositional equalities in an external model establish neither automatically.

For every permitted context substitution `sigma`, also establish that formation and induction commute with reindexing: interpreting the substituted term must agree with reindexing its interpretation. Include motives depending on `n`; a nondependent fold alone does not pass.

The existing committed [Initiality.lean](/Users/oobi/Documents/kanon/meta/KanonMeta/Initiality.lean), `Initial`, `Displayed`, `elim`, and `elim_beta`, supplies the total-algebra argument conditional on chosen folds and uniqueness. It uses external dependent pairs and equality; the beta proof uses function extensionality. Its hypotheses must not be mistaken for a construction of initiality.

**Candidate construction and assumption ledger.** The staged [initial-chain document](/Users/oobi/Documents/kanon/dev/INITIAL-CHAIN.md) reports an external Lean model of the sequence `0, F(0), F(F(0)), ...`, its quotient colimit, and preservation by `1 + X`. The staged [indexed document](/Users/oobi/Documents/kanon/dev/INDEXED-CONSTRUCTION.md) extends this to nullary/unary indexed signatures. These are useful candidates for a later pinned import, not evidence already present in the selected compiler commit.

For the first construction, record each item below as metatheory, object-language derivation, or unresolved assumption:

1. The ambient category and its universe of carriers, with contexts and reindexing.
2. The admitted presentation of the omega diagram and its maps. External Lean Nat may index a semantic construction, but the object presentation must not invoke the N induction being derived.
3. Existence of the required Kan extension or colimit, with its factorization and uniqueness. Lean Quot and equality in an external construction do not establish admissibility inside Kanon's grammar.
4. Preservation of that colimit by `1 + X`, followed by initiality of its induced algebra. Preservation is a theorem to prove, not a general consequence of positivity.
5. The dependent-pair and transport constructions used to turn initiality into induction, together with substitution coherence and computation laws.
6. Any equivalence between constructed `N` and built-in natural literals, plus agreement of every native arithmetic accelerator. Keep this separate from initiality.

General finite branching, infinite branching, nested inductives, universes, and quotients remain subsequent obligations. The omega construction for the unary signature must not be generalized to all Lean inductives without further existence and preservation arguments.

**Smallest next formalization.** Add one independently reviewable `NatFragmentBridge` module in an isolated source snapshot, after pinning the exact chosen metatheory files. It should cover only the closed declaration of `N` and its dependent case/structural-recursion fragment:

1. Mirror the exact accepted SMu declaration, constructor addresses, branch-field order, and motive binders for this signature. Define a small typed judgment for this fragment and an adapter to the Unit-indexed polynomial `1 + X`; do not use a string name alone as the adapter's evidence.
2. Interpret zero, successor, and dependent branches in the candidate algebra. Prove the two source case-beta steps preserve that interpretation, and prove the guarded recursive definition realizes the displayed eliminator, explicitly conditional on initiality at this intermediate stage.
3. Prove typed substitution for this fragment, including a motive depending on the scrutinee. Include a wrong-index/ill-scoped rejection example and a nonconstant observation separating zero from successor zero.
4. Publish the remaining construction-admissibility premise explicitly. The intermediate bridge is complete only for its stated conditional theorem; the Kan-only milestone remains open until that premise is discharged from the admitted grammar and the relevant computational rules are justified.

Do not repeat an external Nat-initiality test as the proposed advance. The new evidence must connect actual admitted syntax and operations to the model. An accompanying rule inventory must distinguish source-level derived operations from assumptions supplied by Lean's metatheory.

**Evidence boundaries.** A Telcoin backend prototype can demonstrate artifact generation and observed execution. It cannot prove the Kan foundation, the checker, erasure, or backend correct in general. The eventual expressiveness claim needs a translation from a pinned Lean calculus; safety needs its own soundness argument. Neither a passing counter contract nor this first Nat fragment establishes either complete claim or OCaml compilation-speed parity.

**Conditional bridge progress, 2026-09-07.** The first bounded implementation
is now in [KanonTelcoin/NatFragmentBridge.lean](KanonTelcoin/NatFragmentBridge.lean),
using an exact copied `Initiality.lean` from the compiler pin. The
[bridge specification](NAT-FRAGMENT-BRIDGE.md) records its theorem API and
remaining premises. It covers `N`-valued local contexts with typed semantic
motive and branch parameters, dependent case beta, substitution with
transport, and closed structural source evaluation agreeing with the
displayed eliminator under `Initial`.

An OCaml adapter validates the real pinned compiler's family, case, and
recursive-function structures. Its source fixture uses a varying dependent
family and no builtin `Nat` or arithmetic. The executable source/profile
agreement is a regression check, not a verified implementation of the Lean
judgments by the OCaml checker. General mixed contexts and arbitrary branch
expressions remain outside this formal fragment.

The next foundation task is to discharge construction admissibility and
connect the chosen Kan construction to this explicit initiality premise.
Extending the syntax adapter's correctness argument, the native natural
accelerator agreement, and broader dependent syntax remain separate work.

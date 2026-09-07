# Source evidence for NatFragmentBridge

The [fixture](fixtures/nat-fragment.kanon) is checked by the pinned
`Kanon_surface.Elab.check_in` and `Kanon_kernel`, starting with `Global.empty`.
It uses the declared unary family `N`, with no builtin `Nat`, arithmetic
primitives, user axioms, parameters, or indices. The EVM frontend admission
policy is unchanged.

The [adapter](../lib/nat_fragment.ml) admits only the selected source schemas.
It reads the actual checked family table and validates its constructor status,
positivity flag, Type0 level, field types, quantities, arities, and result
indices. The flag is evidence of the pinned checker's admission, not a proof
of initiality. The source representations are:

| Source component | Exact representation |
| --- | --- |
| Family type | `Lan (SMu ("N", []), Sec (SColl 0, []))` |
| Zero | `In (SMu ("N", []), ACtor "zero", [])` |
| Successor | `In (SMu ("N", []), ACtor "succ", [predecessor])` |
| Case scrutinee quantity | `One` |
| Explicit motive | `m_ind = Some "N"`, no index binders, self at DB0 |
| Zero branch | `ACtor "zero"`, no field binders |
| Successor branch | `ACtor "succ"`, one `Many` predecessor at DB0 |

The adapter checks all SMu payloads in the selected definitions and verifies
de Bruijn scope, including annotations that the pinned checker may ignore.
For the selected application and function-type schemas it also checks
annotation typehood and agreement with the inferred function domain and
quantity. Other branch or annotation forms are rejected. Binder display names
may vary; binding positions and quantities carry the evidence.

The generic `induction` definition has outer binders `P,z,s,n`, with `P`
erased and the others unrestricted. Its case uses `n` at DB0. The motive
applies `P` at DB4 to self at DB0; the zero branch returns `z` at DB2. Under
the successor branch, the source is exactly `s predecessor
(induction P z s predecessor)`, with `s` at DB2, `P` at DB4, and `z` at DB3.
There is no implicit induction-hypothesis binder. The adapter reruns the
structural guard and requires its single call to decrease through the
successor branch at recursive parameter position 3.

The fixture includes a genuinely dependent Type0-valued `Fiber`: its zero
fiber is `N`, while its successor fiber is `prod (N, N)`. `dependentCase` and
`recursiveDependent` produce witnesses at those different types. A separate
`double` instance uses the recursive result twice through nested successors.

Run the source regression suite with:

```sh
dunecho test
_build/default/tests/nat_fragment.exe < foundation/fixtures/nat-fragment.kanon
```

The executable reports 37 checks. These include both source case-beta
observations, dependent recursive execution, a nonconstant observation
separating zero from successor zero, typed context variables, wrong indices,
ill-scoped terms, wrong fields and quantities, unguarded recursion, and
malformed application annotations.

The machine-readable profile is emitted only after all these checks succeed:

```sh
_build/default/tests/nat_fragment.exe --profile < foundation/fixtures/nat-fragment.kanon
```

The matching Lean profile and source semantic theorems are described in
[NAT-FRAGMENT-BRIDGE.md](../NAT-FRAGMENT-BRIDGE.md). Profile agreement and
execution regressions connect this fixture to the mirrored schema. They do
not prove the OCaml adapter, elaborator, checker, or evaluator correct in
general. Lean treats the dependent motive and step as semantic parameters;
the full erased `P,z,s,n` context is source regression evidence, not a
formalization of every dependent kernel context. Construction admissibility
and the Kan-only derivation remain open as recorded in
[FOUNDATION-OBLIGATIONS.md](../FOUNDATION-OBLIGATIONS.md).

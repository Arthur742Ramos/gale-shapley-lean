# Gale–Shapley deferred acceptance in Lean 4

This project formalizes the men-proposing deferred-acceptance algorithm for
finite two-sided matching markets with decidable strict preferences. It proves
stable matching existence, termination of the specified run at a stable
matching, and conditional men-optimality: whenever a man is matched to w0 by
the deferred-acceptance outcome, he weakly prefers w0 to every partner with
whom some stable matching pairs him.

The preference relations on each side are irreflexive, transitive, and total
for distinct alternatives. `prefersM` and `prefersW` treat `none` as worse than
every partner. Stability has no separate acceptability condition. The market
sides need not have equal cardinality; the main theorems assume that the women
type is nonempty.

## Files

- `GS/Basic.lean` defines profiles, matchings, preference comparisons, blocking
  pairs, stability, and the deferred-acceptance state and proposal step. It also
  provides the `GS.Palomar` names used by the comparator.
- `GS/Termination.lean` proves finite termination and defines the run.
- `GS/Stability.lean` proves stability and men-optimality properties.
- `GS/Main.lean` contains the proved results under
  `GS.Palomar.Implementation`.
- `Challenge.lean` states the three compared theorems with intentional proof
  holes.
- `Solution.lean` repeats those theorem statements and proves them by applying
  the corresponding results from `GS.Palomar.Implementation`.
- `comparator.json` lists the compared theorem and definition names.
- `LICENSE` records the repository's BSD-3-Clause license.
- `formalization.yaml` records the project scope, source, authorship, and
  theorem alignment.
- `scripts/verify-palomar.sh` builds the modules, checks comparator names and
  declaration kinds, audits theorem axioms, and rejects implementation sorries.

## Build and audit

The project uses Lean 4 and Mathlib `v4.35.0-rc2`.

Comparator compiles Challenge and Solution as separate modules. `Solution.lean`
imports `GS.Main` and declares the target theorem names using the implementation
proofs; importing Challenge there would place the same theorem names in one Lean
environment.

```sh
scripts/verify-palomar.sh
```

The verifier selects the pinned Elan toolchain and runs
`lake build Challenge Solution` before the declaration and axiom audits.

The local `#print axioms` audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for each compared theorem. `Solution.lean` and `GS/` contain no
`sorry` declarations.

## Palomar status

The local packaging checks are provided by `scripts/verify-palomar.sh`. This
work has not been submitted or registered with Palomar.

# The QuadFormsKB subset

This directory holds the modules of Jonathan Hanke's QuadFormsKB that the formalization imports,
directly or indirectly, and nothing else. They are taken from upstream commit `43bd018`
(version 0.6.1, Lean 4.35 / Mathlib v4.35.0) of <https://github.com/jonhanke/quadratic-forms-lean>
and ported to Lean 4.36 / Mathlib v4.36.0. QuadFormsKB is licensed under the Apache License 2.0
(`LICENSE` in this directory); its notice is reproduced in the repository's `NOTICE`.

A file changed by the port begins with the line

```
-- Ported to Lean 4.36 / Mathlib v4.36.0 for this repository; see QuadFormsKB/PORT.md.
```

and is otherwise upstream's file with the changes below. A file without that line is upstream's
file unchanged. The files in `Port/` are new: they restore, under the old statements, a few
Mathlib lemmas that Mathlib v4.36 removed or changed.

## The changes

None changes a statement of the results used (`docs/PROVENANCE.md`). By kind:

* **Mathlib renames and splits.** `Submodule.IsLattice` split into `IsLattice` and
  `IsFullLattice` (the old notion; anonymous constructors through `Port/Lattice.lean`);
  `finset_prod` → `finsetProd`; `NumberField.RingOfIntegers.monicFactorsMod`;
  `ContDiffAt.hasStrictFDerivAt` → `hasStrictFDerivAt_fderiv`; `Xor'` → `Xor`.
* **`padicValNat` and `multiplicity`.** The `padicValNat` lemmas are deprecated aliases of
  `multiplicity` lemmas in v4.36; `Port/PadicVal.lean` keeps the v4.35 statements, and
  `padicValRat`, `padicValInt` and `Nat.factorization_def` are used through `multiplicity`.
* **Removed lemmas.** `Measurable.ennreal_tsum` (`Port/Compat.lean`).
* **Name resolution.** `Matrix.mul_apply` and `Matrix.one_apply` where Mathlib's new root
  `mul_apply` and `one_apply` shadow them; ambiguous `_root_.X` against `NS.X`.
* **Changed structures and signatures.** `QuasiMeasurePreserving` takes `AEMeasurable`; `WithAbs`
  is a structure (`toAbs`, `ofAbs`); `AbsoluteValue.Completion.map` replaces
  `LiesOver.completionMap`; `Module.Free` and `Module.Finite` of a lattice are no longer
  instances; `Ring.HasFiniteQuotients`; `natDegree_X_pow_sub_C` takes its argument explicitly.
* **Elaboration time.** In v4.36, `congr` retries leftover goals by `rfl` at default
  transparency, which unfolds products over the infinite places, theta series and integrals: in
  the declarations that timed out, `congr N` runs under `with_reducible`, or the heartbeat limit is
  raised. Pointwise `Continuous.add`, `Measurable.mul` and similar lemmas now conclude `f + g`;
  where unifying with an explicit function unfolded numerals of `ℝ` and `ℂ`, the inner function is
  proved separately and transported by `.congr fun _ => rfl`. Slow `rfl` through subgroup
  coercions uses `Subgroup.subtype_apply` and `Subgroup.coe_mul`; slow `set` uses `let` and an
  explicit equation.
* **Declarations.** `noncomputable section` where v4.36 requires it; `{x | p ∧ q}` against
  `s ∩ t`; delayed projections written `by exact`.

If upstream QuadFormsKB moves to Lean 4.36, this directory can be replaced by a Lake dependency on
it.

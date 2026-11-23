-- Added for the Lean 4.36 port in this repository; see QuadFormsKB/PORT.md.
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Compatibility lemmas for the port to Mathlib v4.36

Mathlib v4.36 no longer has `Measurable.ennreal_tsum`. This file restores it with its former
statement, proved from `tsum_eq_iSup_sum`.
-/

open scoped ENNReal

/-- A countable sum of measurable `ℝ≥0∞`-valued functions is measurable. -/
theorem Measurable.ennreal_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f : ι → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  simp_rw [tsum_eq_iSup_sum]
  exact Measurable.iSup fun s => Finset.measurable_sum s fun i _ => h i

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Roots of `Iₙ` and the form of `A₂`

Used by `prop:exception` (roots of `I₆`, `KimKimOh/Quinary/Core.lean`).

* `root_support`: a vector of norm 2 in `Iₙ` is `±eᵢ ± eⱼ` with `i ≠ j`.
* `bilinA2`, the bilinear form of `A₂`: `Q(w) = 2(w₀² - w₀w₁ + w₁²)` (`bilinA2_self`), and
  `w₀² - w₀w₁ + w₁²` is positive away from the origin (`a2_quad_nonneg`, `a2_quad_eq_zero`).
-/

namespace KimKimOh

/-- A root of `Iₙ` is `±eᵢ ± eⱼ` with `i ≠ j`: every entry has square at most 2, so it lies
in `{-1, 0, 1}`, and exactly two entries are nonzero. -/
theorem root_support {n : ℕ} (u : Fin n → ℤ) (hu : ∑ l, u l * u l = 2) :
    ∃ i j : Fin n, i ≠ j ∧ (u i = 1 ∨ u i = -1) ∧ (u j = 1 ∨ u j = -1) ∧
      ∀ l, l ≠ i → l ≠ j → u l = 0 := by
  classical
  have hunit (m : Fin n) : u m = 0 ∨ u m = 1 ∨ u m = -1 := by
    have : u m * u m ≤ 2 := hu ▸ Finset.single_le_sum (f := fun m => u m * u m)
      (fun m _ => mul_self_nonneg (u m)) (Finset.mem_univ m)
    have h1 : -1 ≤ u m := by nlinarith
    have h2 : u m ≤ 1 := by nlinarith
    interval_cases u m <;> simp
  set s := Finset.univ.filter fun l => u l ≠ 0
  have hs : s.card = 2 := by
    have : (s.card : ℤ) = 2 := by
      rw [← hu, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      rcases hunit m with h | h | h <;> simp [h]
    exact_mod_cast this
  obtain ⟨i, j, hij, hsij⟩ := Finset.card_eq_two.mp hs
  have hmem (l : Fin n) : u l ≠ 0 ↔ l = i ∨ l = j := by
    simpa [s] using congrArg (l ∈ ·) hsij
  refine ⟨i, j, hij, ?_, ?_, fun l hi hj => ?_⟩
  · have := (hmem i).mpr (Or.inl rfl); rcases hunit i with h | h | h <;> simp_all
  · have := (hmem j).mpr (Or.inr rfl); rcases hunit j with h | h | h <;> simp_all
  · by_contra h; rcases (hmem l).mp h with rfl | rfl <;> contradiction

/-- The bilinear form of `A₂`, with Gram matrix `[[2, -1], [-1, 2]]`. -/
def bilinA2 (u v : Fin 2 → ℤ) : ℤ :=
  2 * u 0 * v 0 - u 0 * v 1 - u 1 * v 0 + 2 * u 1 * v 1

@[simp] theorem bilinA2_zero_left (v : Fin 2 → ℤ) : bilinA2 0 v = 0 := by simp [bilinA2]
@[simp] theorem bilinA2_zero_right (v : Fin 2 → ℤ) : bilinA2 v 0 = 0 := by simp [bilinA2]

theorem bilinA2_self (w : Fin 2 → ℤ) : bilinA2 w w = 2 * (w 0 ^ 2 - w 0 * w 1 + w 1 ^ 2) := by
  unfold bilinA2; ring

theorem a2_quad_nonneg (x y : ℤ) : 0 ≤ x ^ 2 - x * y + y ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

theorem bilinA2_self_ge (w : Fin 2 → ℤ) : w 0 ^ 2 + w 1 ^ 2 ≤ bilinA2 w w := by
  rw [bilinA2_self]; nlinarith [sq_nonneg (w 0 - w 1)]

theorem a2_quad_eq_zero {w : Fin 2 → ℤ} (h : w 0 ^ 2 - w 0 * w 1 + w 1 ^ 2 = 0) : w = 0 := by
  have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0 - w 1), sq_nonneg (w 0), sq_nonneg (w 1)]
  have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0 - w 1), sq_nonneg (w 0), sq_nonneg (w 1)]
  funext k; fin_cases k <;> simpa

end KimKimOh

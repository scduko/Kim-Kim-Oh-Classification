import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.NormNum

/-!
# Primes at least 5

At a prime `p ≥ 5` the hosts `K₃`, `K₉` are unimodular (`lem:functional`), and §§2–4 use repeatedly
that such a prime divides none of the small integers that occur as scales, determinants and steps.

* `prime_cases`: a prime is `2`, `3` or at least `5`;
* `not_dvd_of_lt_five`: `p ≥ 5` does not divide an integer `0 < n < 5`;
* `not_dvd_of_dvd_two_three`: a prime `p ≥ 5` divides no divisor of `2ᵃ 3ᵇ`; in particular
  none of `1, 2, 3, 4, 6, 9` (`not_dvd_small`) and none of `±1, ±2, ±3, ±6`
  (`not_dvd_of_divisor_six`).
-/

namespace KimKimOh

/-- A prime is `2`, `3` or at least `5`. -/
theorem prime_cases {p : ℕ} (hp : p.Prime) : p = 2 ∨ p = 3 ∨ 5 ≤ p := by
  by_cases h2 : p = 2
  · exact Or.inl h2
  by_cases h3 : p = 3
  · exact Or.inr (Or.inl h3)
  exact Or.inr (Or.inr (hp.five_le_of_ne_two_of_ne_three h2 h3))

/-- `p ≥ 5` does not divide an integer `0 < n < 5`. -/
theorem not_dvd_of_lt_five {p : ℕ} (h5 : 5 ≤ p) {n : ℤ} (h0 : 0 < n) (h4 : n < 5) :
    ¬ (p : ℤ) ∣ n := fun hd => by
  have := Int.le_of_dvd h0 hd
  omega

/-- A prime `p ≥ 5` divides no divisor of `2ᵃ 3ᵇ`. -/
theorem not_dvd_of_dvd_two_three {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {n a b : ℕ}
    (hn : n ∣ 2 ^ a * 3 ^ b) : ¬ p ∣ n := fun h => by
  rcases (Nat.Prime.dvd_mul hp).mp (h.trans hn) with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega

/-- A prime `p ≥ 5` divides none of `1, 2, 3, 4, 6, 9`. -/
theorem not_dvd_small {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {n : ℤ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 9) : ¬ (p : ℤ) ∣ n := fun h =>
  not_dvd_of_dvd_two_three hp h5 (a := 2) (b := 2)
    (by rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (Int.natCast_dvd.mp h)

/-- A prime `p ≥ 5` divides none of the signed divisors of 6. -/
theorem not_dvd_of_divisor_six {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {n : ℤ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 ∨ n = -1 ∨ n = -2 ∨ n = -3 ∨ n = -6) :
    ¬ (p : ℤ) ∣ n := fun h =>
  not_dvd_of_dvd_two_three hp h5 (a := 1) (b := 1)
    (by rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (Int.natCast_dvd.mp h)

end KimKimOh

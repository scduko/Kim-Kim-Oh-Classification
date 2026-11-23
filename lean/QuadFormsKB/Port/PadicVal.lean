-- Added for the Lean 4.36 port in this repository; see QuadFormsKB/PORT.md.
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# `padicValNat` lemmas with their Mathlib v4.35 statements

In Mathlib v4.36 the lemmas below are deprecated aliases of `multiplicity` lemmas, so their
conclusions mention `multiplicity p n` where the library's statements mention `padicValNat p n`.
The primed versions here keep the v4.35 statements; they follow from the new ones by
`Nat.padicValNat_def : padicValNat p n = multiplicity p n`.
-/

set_option linter.deprecated false

open Nat

variable {p : ℕ}

namespace padicValNat

theorem eq_zero_of_not_dvd' {n : ℕ} (h : ¬p ∣ n) : padicValNat p n = 0 := by
  rw [padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd h

theorem dvd_of_ne_zero' {n : ℕ} (h : padicValNat p n ≠ 0) : p ∣ n := by
  rw [padicValNat_def] at h; exact padicValNat.dvd_of_ne_zero h

theorem eq_zero_iff' {n : ℕ} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  rw [padicValNat_def]; exact padicValNat.eq_zero_iff

theorem self' (hp : 1 < p) : padicValNat p p = 1 := by
  rw [padicValNat_def]; exact padicValNat.self hp

protected theorem mul' {a b : ℕ} [Fact p.Prime] (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (a * b) = padicValNat p a + padicValNat p b := by
  simp only [padicValNat_def]; exact padicValNat.mul ha hb

protected theorem pow' [Fact p.Prime] (a n : ℕ) : padicValNat p (a ^ n) = n * padicValNat p a := by
  simp only [padicValNat_def]; exact padicValNat.pow a n

protected theorem prime_pow' [Fact p.Prime] (n : ℕ) : padicValNat p (p ^ n) = n := by
  rw [padicValNat_def]; exact padicValNat.prime_pow n

end padicValNat

theorem padicValNat_self' [Fact p.Prime] : padicValNat p p = 1 := by
  rw [padicValNat_def]; exact padicValNat_self

theorem one_le_padicValNat_of_dvd' {n : ℕ} [Fact p.Prime] (hn : n ≠ 0) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rw [padicValNat_def]; exact one_le_padicValNat_of_dvd hn div

theorem padicValNat_dvd_iff_le' [Fact p.Prime] {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a := by
  rw [padicValNat_def]; exact padicValNat_dvd_iff_le ha

theorem padicValNat_dvd_iff' (n : ℕ) [Fact p.Prime] (a : ℕ) :
    p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a := by
  rw [padicValNat_def]; exact padicValNat_dvd_iff n a

theorem pow_padicValNat_dvd' {n : ℕ} : p ^ padicValNat p n ∣ n := by
  rw [padicValNat_def]; exact pow_multiplicity_dvd p n

theorem padicValNat_primes' {q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p ≠ q) :
    padicValNat p q = 0 := by
  rw [padicValNat_def]; exact padicValNat_primes ne

theorem padicValNat_le_self' (n : ℕ) : padicValNat p n ≤ n := by
  rw [padicValNat_def]; exact padicValNat_le_self n

theorem padicValNat_factorial' {n b : ℕ} [Fact p.Prime] (hnb : log p n < b) :
    padicValNat p (n !) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  rw [padicValNat_def]; exact padicValNat_factorial hnb

theorem padicValNat_factorial_mul' (n : ℕ) [Fact p.Prime] :
    padicValNat p (p * n)! = padicValNat p n ! + n := by
  simp only [padicValNat_def]; exact padicValNat_factorial_mul n

theorem sub_one_mul_padicValNat_factorial_lt_of_ne_zero' [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial < n := by
  rw [padicValNat_def]; exact sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn

theorem prod_pow_prime_padicValNat' (n : ℕ) (hn : n ≠ 0) (m : ℕ) (pr : n < m) :
    ∏ p ∈ Finset.range m with p.Prime, p ^ padicValNat p n = n := by
  simp only [padicValNat_def]; exact prod_pow_prime_padicValNat n hn m pr

theorem padicValRat.of_nat' {n : ℕ} : padicValRat p n = padicValNat p n := by
  rw [padicValNat_def]; exact padicValRat.of_nat

theorem padicValInt.of_nat' {n : ℕ} : padicValInt p n = padicValNat p n := by
  rw [padicValNat_def]; exact padicValInt.of_nat

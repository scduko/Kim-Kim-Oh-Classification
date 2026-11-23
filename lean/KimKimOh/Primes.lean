import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Associated
import KimKimOh.Compute.Primes

/-!
# The primes from 5 (`sec:high`)

`q i` is the `i`-th prime at least 5 (`q 0 = 5`, `q 1 = 7`, …) and `P t = q₀ ⋯ q_{t-1}`. The
paper indexes from 1, `q_1 = 5`, so its `q_{i+1}` is `q i` here and `P_t` is `P t`.

* An element `p` of a finite set `S` of such primes with `r` smaller elements in `S` is at least
  `q r` (`q_le_of_rank`). Hence, for `f` antitone from 5 on, `Σ_{p ∈ S} f p ≤ Σ_{i < |S|} f (q i)`
  (`sum_le_sum_q`), and `∏_{p ∈ S} p ≥ P |S|` (`prod_ge_P`).
* So a positive integer below `P (t + 1)` has at most `t` prime factors at least 5
  (`card_le_of_lt_P`): "Every positive integer at most `δ` has at most `t` distinct prime divisors
  at least `5`."
* The values `q 0, …, q 27` (`q_eq_list`).
-/

namespace KimKimOh.Primes

open Finset

/-- `n` is a prime at least 5. -/
def IsQ (n : ℕ) : Prop := n.Prime ∧ 5 ≤ n

instance : DecidablePred IsQ := fun n => inferInstanceAs (Decidable (n.Prime ∧ 5 ≤ n))

theorem infinite_isQ : (Set.ofPred IsQ).Infinite :=
  Set.infinite_of_forall_exists_gt fun a => by
    obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (a + 5)
    exact ⟨p, ⟨hpp, by omega⟩, by omega⟩

/-- The `i`-th prime at least 5. -/
noncomputable def q (i : ℕ) : ℕ := Nat.nth IsQ i

/-- `P t = q₀ ⋯ q_{t-1}`. -/
noncomputable def P (t : ℕ) : ℕ := ∏ i ∈ range t, q i

theorem q_isQ (i : ℕ) : IsQ (q i) := Nat.nth_mem_of_infinite infinite_isQ i

theorem q_prime (i : ℕ) : (q i).Prime := (q_isQ i).1

theorem five_le_q (i : ℕ) : 5 ≤ q i := (q_isQ i).2

theorem q_mono : Monotone q := Nat.nth_monotone infinite_isQ

theorem q_strictMono : StrictMono q := Nat.nth_strictMono infinite_isQ

/-- `q (count IsQ n) = n` for a prime `n ≥ 5`. -/
theorem q_count {n : ℕ} (h : IsQ n) : q (Nat.count IsQ n) = n := Nat.nth_count h

/-- **Ranks.** If every element of `S` is a prime at least 5, an element `p` of `S` with `r`
smaller elements of `S` is at least `q r`. -/
theorem q_le_of_rank {S : Finset ℕ} (hS : ∀ p ∈ S, IsQ p) {p : ℕ} (hp : p ∈ S) :
    q (S.filter (· < p)).card ≤ p := by
  have hc : (S.filter (· < p)).card ≤ Nat.count IsQ p := by
    rw [Nat.count_eq_card_filter_range]
    refine card_le_card fun x hx => ?_
    simp only [mem_filter, mem_range] at hx ⊢
    exact ⟨hx.2, hS x hx.1⟩
  calc q _ ≤ q (Nat.count IsQ p) := q_mono hc
    _ = p := q_count (hS p hp)

/-- The largest element of `S` has `|S| - 1` smaller elements, so is at least `q (|S| - 1)`. -/
theorem q_le_max {T : Finset ℕ} {m : ℕ} (hS : ∀ p ∈ insert m T, IsQ p) (hT : ∀ x ∈ T, x < m) :
    q T.card ≤ m := by
  have hm : m ∈ insert m T := mem_insert_self m T
  have h := q_le_of_rank hS hm
  have e : (insert m T).filter (· < m) = T := by
    ext x
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | hx, hlt⟩
      · exact absurd hlt (lt_irrefl _)
      · exact hx
    · intro hx; exact ⟨Or.inr hx, hT x hx⟩
  rwa [e] at h

/-- **Sums over primes from 5.** For antitone `f`, `Σ_{p ∈ S} f p ≤ Σ_{i < |S|} f (q i)`. -/
theorem sum_le_sum_q {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    (f : ℕ → M) (hf : ∀ a b, 5 ≤ a → a ≤ b → f b ≤ f a) :
    ∀ S : Finset ℕ, (∀ p ∈ S, IsQ p) → ∑ p ∈ S, f p ≤ ∑ i ∈ range S.card, f (q i) := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert m T hT ih =>
    intro hS
    have hmT : m ∉ T := fun h => lt_irrefl _ (hT m h)
    rw [sum_insert hmT, card_insert_of_notMem hmT, sum_range_succ, add_comm]
    exact add_le_add (ih fun p hp => hS p (mem_insert_of_mem hp)) (hf _ _ (five_le_q _) (q_le_max hS hT))

/-- **Products over primes from 5.** `∏_{p ∈ S} p ≥ P |S|`. -/
theorem prod_ge_P : ∀ S : Finset ℕ, (∀ p ∈ S, IsQ p) → P S.card ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _; simp [P]
  | insert m T hT ih =>
    intro hS
    have hmT : m ∉ T := fun h => lt_irrefl _ (hT m h)
    rw [prod_insert hmT, card_insert_of_notMem hmT, P, prod_range_succ, mul_comm]
    exact Nat.mul_le_mul (q_le_max hS hT) (ih fun p hp => hS p (mem_insert_of_mem hp))

/-- **At most `t` prime factors from 5.** If the product of a set `S` of primes from 5 is
below `P (t + 1)`, then `|S| ≤ t`. -/
theorem card_le_of_prod_lt {S : Finset ℕ} (hS : ∀ p ∈ S, IsQ p) {t : ℕ}
    (h : ∏ p ∈ S, p < P (t + 1)) : S.card ≤ t := by
  by_contra hlt
  push Not at hlt
  have hmono : P (t + 1) ≤ P S.card := by
    rw [P, P]
    exact prod_le_prod_of_subset_of_one_le (range_subset_range.mpr hlt)
      (fun i _ _ => by have := five_le_q i; omega)
  exact absurd (hmono.trans (prod_ge_P S hS)) (not_le.mpr h)

/-- The primes from 5 dividing a positive integer `n` have product at most `n`. -/
theorem prod_primeFactors_le {n : ℕ} (hn : 0 < n) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ n) :
    ∏ p ∈ S, p ≤ n := by
  have hdvd : ∏ p ∈ S, p ∣ n := by
    refine Finset.prod_primes_dvd n (fun p hp => (hS p hp).1.prime) (fun p hp => (hS p hp).2)
  exact Nat.le_of_dvd hn hdvd

/-- A positive integer below `P (t + 1)` has at most `t` prime factors from 5. -/
theorem card_le_of_lt_P {n t : ℕ} (hn : 0 < n) (hlt : n < P (t + 1)) (S : Finset ℕ)
    (hS : ∀ p ∈ S, IsQ p ∧ p ∣ n) : S.card ≤ t :=
  card_le_of_prod_lt (fun p hp => (hS p hp).1)
    ((prod_primeFactors_le hn S fun p hp => ⟨(hS p hp).1.1, (hS p hp).2⟩).trans_lt hlt)

/-! ### The first primes from 5 -/

theorem qList_isQ : ∀ n ∈ qList, IsQ n := by decide

theorem count_qList : ∀ i (h : i < qList.length), Nat.count IsQ qList[i] = i := by decide +kernel

/-- `q i` is the `i`-th entry of `qList`, for `i < 28`. -/
theorem q_eq_list {i : ℕ} (hi : i < qList.length) : q i = qList[i] := by
  have h := q_count (qList_isQ _ (List.getElem_mem hi))
  rwa [count_qList i hi] at h

end KimKimOh.Primes

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Excluded residue classes

The sieves of `sec:high` and `sec:finite` exclude, at each prime `p ≥ 5`, at most `ν_p` classes of
`k` modulo `p` (`lem:scalar-slice`). `AtMostClasses p ν bad` says that `bad` holds on at most `ν`
residue classes modulo `p`, and `Periodic p bad` that it depends only on the class modulo `p`.
`card_badResidues_le` counts the bad residues of an interval of length `p`.
-/

namespace KimKimOh.Excluded

/-- `bad` holds on at most `ν` residue classes modulo `p`: among any `ν + 1` pairwise
incongruent integers, one is not bad. -/
def AtMostClasses (p ν : ℕ) (bad : ℤ → Prop) : Prop :=
  ∀ ks : List ℤ, ks.length = ν + 1 → ks.Pairwise (fun u v => ¬ (p : ℤ) ∣ u - v) →
    ∃ k ∈ ks, ¬ bad k

/-- `bad` depends only on the residue modulo `p`. -/
def Periodic (p : ℕ) (bad : ℤ → Prop) : Prop :=
  ∀ k k' : ℤ, (p : ℤ) ∣ k - k' → (bad k ↔ bad k')

/-- Distinct naturals below `p` are incongruent modulo `p`. -/
theorem not_dvd_sub_of_lt {p a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    ¬ (p : ℤ) ∣ (a : ℤ) - b := by
  intro h
  have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
  omega

/-- The residues `ρ < p` with `bad (k₀ + ρ)` number at most `ν`. -/
theorem card_badResidues_le {p ν : ℕ} {bad : ℤ → Prop} [DecidablePred bad]
    (hν : AtMostClasses p ν bad) (k₀ : ℤ) :
    ((Finset.range p).filter fun ρ : ℕ => bad (k₀ + (ρ : ℤ))).card ≤ ν := by
  by_contra hlt
  push Not at hlt
  set Q := (Finset.range p).filter fun ρ : ℕ => bad (k₀ + (ρ : ℤ))
  obtain ⟨T, hTQ, hT⟩ := Finset.exists_subset_card_eq (show ν + 1 ≤ Q.card by omega)
  have hTp (ρ : ℕ) (hρ : ρ ∈ T) : ρ < p := Finset.mem_range.mp (Finset.mem_filter.mp (hTQ hρ)).1
  obtain ⟨k, hk, hbad⟩ := hν (T.toList.map fun ρ : ℕ => k₀ + (ρ : ℤ)) (by simp [hT]) (by
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (R := fun a b : ℕ => a ≠ b) ?_ (Finset.nodup_toList T)
    intro a b ha hb hab hdvd
    rw [Finset.mem_toList] at ha hb
    apply not_dvd_sub_of_lt (hTp a ha) (hTp b hb) hab
    rwa [show k₀ + (a : ℤ) - (k₀ + b) = (a : ℤ) - b by ring] at hdvd)
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hk
  exact hbad (Finset.mem_filter.mp (hTQ (Finset.mem_toList.mp hρ))).2


end KimKimOh.Excluded

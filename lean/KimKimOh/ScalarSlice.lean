import KimKimOh.Correction
import KimKimOh.ExcludedClasses
import Mathlib.Algebra.Field.ZMod

/-!
# `lem:scalar-slice`

Let `p ≥ 5`, let `G ≢ 0 (mod p)`, and fix `α = (x, y)`. Write `B' = B - s ααᵀ` and
`Δ = det B'`. The correction `C = G - s λλᵀ`, `λ = (x, y, k)`:

* has rank at least 2 modulo `p` for every `k` if `p ∤ Δ` (`Tern.rankGeTwoMod_corr`);
* has rank at most 1 for at most two residues of `k` if `(B, α) ≢ (0, 0)` (`scalar_slice`);
* and for at most one if moreover `p ∤ δ`, or `B ≡ 0`, or `B' ≡ 0` (`scalar_slice_one`).

The proof is the paper's. Rank at most 1 makes the Gram determinant of `C` on `(v, 0)` and
`e₃` vanish (`Tern.gramDet2`, a combination of 2×2 minors). In terms of `G` this determinant is
`-s B(v,v) k² + 2 s A R k + (B(v,v) - s A²) f - R²`, with `A = αᵀ v` and `R = rᵀ v`
(`Tern.gramDet2_corr`), and a suitable `v` makes it a polynomial in `k` with at most two
roots, or at most one.
-/

namespace KimKimOh

open Excluded

namespace Tern

/-- The Gram determinant of `g` on the vectors `(v₁, v₂, 0)` and `e₃`. -/
def gramDet2 (g : Tern) (v₁ v₂ : ℤ) : ℤ :=
  (g.a * v₁ * v₁ + 2 * g.b * v₁ * v₂ + g.c * v₂ * v₂) * g.f - (g.d * v₁ + g.e * v₂) ^ 2

/-- Rank at most 1 modulo `p` kills every such Gram determinant: it is a combination of the
minors `af - d²`, `bf - de`, `cf - e²`. -/
theorem dvd_gramDet2 {g : Tern} {p : ℕ} (h : g.RankLeOneMod p) (v₁ v₂ : ℤ) :
    (p : ℤ) ∣ g.gramDet2 v₁ v₂ := by
  have e : g.gramDet2 v₁ v₂ = v₁ ^ 2 * (g.a * g.f - g.d * g.d) +
      2 * v₁ * v₂ * (g.b * g.f - g.d * g.e) + v₂ ^ 2 * (g.c * g.f - g.e * g.e) := by
    unfold gramDet2; ring
  have h2 := h _ (by simp [minors] : g.a * g.f - g.d * g.d ∈ g.minors)
  have h3 := h _ (by simp [minors] : g.c * g.f - g.e * g.e ∈ g.minors)
  have h6 := h _ (by simp [minors] : g.b * g.f - g.d * g.e ∈ g.minors)
  rw [e]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h6 _))
    (dvd_mul_of_dvd_right h3 _)

/-- The Gram determinant of the correction, as a polynomial in `k`. -/
theorem gramDet2_corr (g : Tern) (s x y k v₁ v₂ : ℤ) :
    (g.corr s x y k).gramDet2 v₁ v₂ =
      -s * (g.a * v₁ * v₁ + 2 * g.b * v₁ * v₂ + g.c * v₂ * v₂) * k ^ 2 +
        2 * s * (x * v₁ + y * v₂) * (g.d * v₁ + g.e * v₂) * k +
        ((g.a * v₁ * v₁ + 2 * g.b * v₁ * v₂ + g.c * v₂ * v₂ - s * (x * v₁ + y * v₂) ^ 2) * g.f -
          (g.d * v₁ + g.e * v₂) ^ 2) := by
  unfold gramDet2 corr; ring

end Tern

section Roots

variable {F : Type*} [Field F]

/-- A quadratic with nonzero leading coefficient has no three distinct roots. -/
theorem quad_not_three {α β γ k₁ k₂ k₃ : F} (hα : α ≠ 0) (h12 : k₁ ≠ k₂) (h13 : k₁ ≠ k₃)
    (h23 : k₂ ≠ k₃) (r₁ : α * k₁ ^ 2 + β * k₁ + γ = 0) (r₂ : α * k₂ ^ 2 + β * k₂ + γ = 0)
    (r₃ : α * k₃ ^ 2 + β * k₃ + γ = 0) : False := by
  have e₁ : (k₁ - k₂) * (α * (k₁ + k₂) + β) = 0 := by linear_combination r₁ - r₂
  have e₂ : (k₁ - k₃) * (α * (k₁ + k₃) + β) = 0 := by linear_combination r₁ - r₃
  have f₁ := (mul_eq_zero.mp e₁).resolve_left (sub_ne_zero.mpr h12)
  have f₂ := (mul_eq_zero.mp e₂).resolve_left (sub_ne_zero.mpr h13)
  have : α * (k₂ - k₃) = 0 := by linear_combination f₁ - f₂
  exact h23 (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα))

/-- A polynomial `β k + γ`, not identically zero, has no two distinct roots. -/
theorem lin_not_two {β γ k₁ k₂ : F} (hne : β ≠ 0 ∨ γ ≠ 0) (h12 : k₁ ≠ k₂)
    (r₁ : β * k₁ + γ = 0) (r₂ : β * k₂ + γ = 0) : False := by
  have e : β * (k₁ - k₂) = 0 := by linear_combination r₁ - r₂
  rcases (mul_eq_zero.mp e) with hβ | hk
  · rcases hne with h | h
    · exact h hβ
    · exact h (by rw [hβ] at r₁; simpa using r₁)
  · exact h12 (sub_eq_zero.mp hk)

/-- `-(σ k - ρ)²` with `σ ≠ 0` has no two distinct roots. -/
theorem sq_not_two {σ ρ k₁ k₂ : F} (hσ : σ ≠ 0) (h12 : k₁ ≠ k₂)
    (r₁ : -(σ * k₁ - ρ) ^ 2 = 0) (r₂ : -(σ * k₂ - ρ) ^ 2 = 0) : False := by
  have a₁ : σ * k₁ - ρ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (neg_eq_zero.mp r₁)
  have a₂ : σ * k₂ - ρ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (neg_eq_zero.mp r₂)
  have : σ * (k₁ - k₂) = 0 := by linear_combination a₁ - a₂
  exact h12 (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hσ))

end Roots

section Slice

variable {p : ℕ}

local notation "𝔽" => ZMod p

theorem cast_eq_zero_iff (z : ℤ) : (z : 𝔽) = 0 ↔ (p : ℤ) ∣ z :=
  ZMod.intCast_zmod_eq_zero_iff_dvd z p

theorem cast_ne_of_not_dvd {u v : ℤ} (h : ¬ (p : ℤ) ∣ u - v) : (u : 𝔽) ≠ (v : 𝔽) := by
  intro e
  apply h
  rw [← cast_eq_zero_iff]
  push_cast
  rw [e, sub_self]

/-- The norm `B(v, v)` of `v = (v₁, v₂)` under the leading binary block. -/
def bnorm (g : Tern) (v₁ v₂ : ℤ) : ℤ := g.a * v₁ * v₁ + 2 * g.b * v₁ * v₂ + g.c * v₂ * v₂

/-- Rank at most 1 makes the Gram polynomial vanish at `k` in `ZMod p`. -/
theorem root_of_rankLe (g : Tern) (s x y k v₁ v₂ : ℤ) (h : (g.corr s x y k).RankLeOneMod p) :
    (-(s : 𝔽) * (bnorm g v₁ v₂ : 𝔽)) * (k : 𝔽) ^ 2 +
        (2 * s * ((x * v₁ + y * v₂ : ℤ) : 𝔽) * ((g.d * v₁ + g.e * v₂ : ℤ) : 𝔽)) * (k : 𝔽) +
      (((bnorm g v₁ v₂ : 𝔽) - s * ((x * v₁ + y * v₂ : ℤ) : 𝔽) ^ 2) * (g.f : 𝔽) -
        ((g.d * v₁ + g.e * v₂ : ℤ) : 𝔽) ^ 2) = 0 := by
  have := (cast_eq_zero_iff (p := p) _).mpr (Tern.dvd_gramDet2 h v₁ v₂)
  rw [Tern.gramDet2_corr] at this
  simp only [bnorm]
  push_cast at this ⊢
  linear_combination this

/-- Two nonzero linear forms on `𝔽²` are both nonzero at one of `(1, 0)`, `(0, 1)`, `(1, 1)`. -/
theorem exists_both_ne [Fact p.Prime] {x y d e : 𝔽} (h1 : x ≠ 0 ∨ y ≠ 0) (h2 : d ≠ 0 ∨ e ≠ 0) :
    ∃ v₁ v₂ : ℤ, x * v₁ + y * v₂ ≠ 0 ∧ d * v₁ + e * v₂ ≠ 0 := by
  by_cases hx : x = 0
  · have hy := h1.resolve_left (not_not.mpr hx)
    by_cases he : e = 0
    · have hd := h2.resolve_right (not_not.mpr he)
      exact ⟨1, 1, by simp [hx, hy], by simp [he, hd]⟩
    · exact ⟨0, 1, by simp [hy], by simp [he]⟩
  · by_cases hd : d = 0
    · have he := h2.resolve_left (not_not.mpr hd)
      by_cases hy : y = 0
      · exact ⟨1, 1, by simp [hx, hy], by simp [hd, he]⟩
      · exact ⟨0, 1, by simp [hy], by simp [he]⟩
    · exact ⟨1, 0, by simp [hx], by simp [hd]⟩

theorem two_ne_zero' (hp5 : 5 ≤ p) : (2 : 𝔽) ≠ 0 := by
  intro h
  have := (cast_eq_zero_iff (p := p) 2).mp (by exact_mod_cast h)
  have := Int.le_of_dvd (by norm_num) this
  omega

theorem s_ne_zero (hp5 : 5 ≤ p) {s : ℤ} (hs : s = 1 ∨ s = 2) : (s : 𝔽) ≠ 0 := by
  rcases hs with rfl | rfl
  · have : Fact (1 < p) := ⟨by omega⟩
    simp
  · exact_mod_cast two_ne_zero' hp5

/-- A nonzero binary form over `𝔽`, `p ≥ 5`, has a vector of nonzero norm among `(1, 0)`,
`(0, 1)`, `(1, 1)`. -/
theorem exists_aniso [Fact p.Prime] (hp5 : 5 ≤ p) {g : Tern}
    (h : ¬ ((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c)) :
    ∃ v₁ v₂ : ℤ, (bnorm g v₁ v₂ : 𝔽) ≠ 0 := by
  by_cases ha : (p : ℤ) ∣ g.a
  · by_cases hc : (p : ℤ) ∣ g.c
    · have hb : ¬ (p : ℤ) ∣ g.b := fun hb => h ⟨ha, hb, hc⟩
      refine ⟨1, 1, ?_⟩
      have ha' := (cast_eq_zero_iff (p := p) _).mpr ha
      have hc' := (cast_eq_zero_iff (p := p) _).mpr hc
      have hb' : (g.b : 𝔽) ≠ 0 := fun e => hb ((cast_eq_zero_iff _).mp e)
      simp only [bnorm]
      push_cast
      rw [ha', hc']
      simpa using mul_ne_zero (two_ne_zero' hp5) hb'
    · refine ⟨0, 1, ?_⟩
      simp only [bnorm]
      push_cast
      simpa using fun e => hc ((cast_eq_zero_iff _).mp e)
  · refine ⟨1, 0, ?_⟩
    simp only [bnorm]
    push_cast
    simpa using fun e => ha ((cast_eq_zero_iff _).mp e)

/-- The three residues of a list of pairwise incongruent integers of length 3. -/
theorem three_distinct {k₁ k₂ k₃ : ℤ}
    (h : [k₁, k₂, k₃].Pairwise (fun u v => ¬ (p : ℤ) ∣ u - v)) :
    (k₁ : 𝔽) ≠ k₂ ∧ (k₁ : 𝔽) ≠ k₃ ∧ (k₂ : 𝔽) ≠ k₃ := by
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at h
  exact ⟨cast_ne_of_not_dvd h.1.1, cast_ne_of_not_dvd h.1.2, cast_ne_of_not_dvd h.2⟩

theorem two_distinct {k₁ k₂ : ℤ} (h : [k₁, k₂].Pairwise (fun u v => ¬ (p : ℤ) ∣ u - v)) :
    (k₁ : 𝔽) ≠ k₂ := by
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at h
  exact cast_ne_of_not_dvd h

/-- **The case `B ≡ 0`.** If `B ≡ 0 (mod p)`, `α ≢ 0` and `G ≢ 0`, two incongruent `k` cannot
both give rank at most 1. -/
theorem not_two_of_B_zero [Fact p.Prime] (hp5 : 5 ≤ p) {s : ℤ} (hs : s = 1 ∨ s = 2)
    (g : Tern) (x y : ℤ) (hG : g.NonzeroMod p)
    (ha : (p : ℤ) ∣ g.a) (hb : (p : ℤ) ∣ g.b) (hc : (p : ℤ) ∣ g.c)
    (hα : ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y)) {k₁ k₂ : ℤ} (h12 : (k₁ : 𝔽) ≠ k₂)
    (b₁ : (g.corr s x y k₁).RankLeOneMod p) (b₂ : (g.corr s x y k₂).RankLeOneMod p) : False := by
  have hs0 := s_ne_zero hp5 hs
  have ha' := (cast_eq_zero_iff (p := p) _).mpr ha
  have hb' := (cast_eq_zero_iff (p := p) _).mpr hb
  have hc' := (cast_eq_zero_iff (p := p) _).mpr hc
  have hB : ∀ v₁ v₂ : ℤ, (bnorm g v₁ v₂ : 𝔽) = 0 := fun v₁ v₂ => by
    simp only [bnorm]; push_cast; rw [ha', hb', hc']; ring
  have hα' : (x : 𝔽) ≠ 0 ∨ (y : 𝔽) ≠ 0 := by
    by_contra h0
    simp only [not_or, not_not] at h0
    exact hα ⟨(cast_eq_zero_iff _).mp h0.1, (cast_eq_zero_iff _).mp h0.2⟩
  by_cases hr : (g.d : 𝔽) ≠ 0 ∨ (g.e : 𝔽) ≠ 0
  · obtain ⟨v₁, v₂, hA, hR⟩ := exists_both_ne hα' hr
    have r₁ := root_of_rankLe g s x y k₁ v₁ v₂ b₁
    have r₂ := root_of_rankLe g s x y k₂ v₁ v₂ b₂
    rw [hB] at r₁ r₂
    push_cast at r₁ r₂ hA hR
    refine lin_not_two (β := 2 * (s : 𝔽) * (x * v₁ + y * v₂) * (g.d * v₁ + g.e * v₂))
      (γ := (0 - (s : 𝔽) * (x * v₁ + y * v₂) ^ 2) * g.f - (g.d * v₁ + g.e * v₂) ^ 2)
      (Or.inl ?_) h12 (by linear_combination r₁) (by linear_combination r₂)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (two_ne_zero' hp5) hs0) hA) hR
  · simp only [not_or, not_not] at hr
    have hf : (g.f : 𝔽) ≠ 0 := by
      intro hf
      exact hG ⟨ha, hb, hc, (cast_eq_zero_iff _).mp hr.1, (cast_eq_zero_iff _).mp hr.2,
        (cast_eq_zero_iff _).mp hf⟩
    obtain ⟨v₁, v₂, hA⟩ : ∃ v₁ v₂ : ℤ, ((x * v₁ + y * v₂ : ℤ) : 𝔽) ≠ 0 := by
      rcases hα' with h | h
      · exact ⟨1, 0, by push_cast; simpa using h⟩
      · exact ⟨0, 1, by push_cast; simpa using h⟩
    have r₁ := root_of_rankLe g s x y k₁ v₁ v₂ b₁
    rw [hB] at r₁
    push_cast at r₁ hA
    rw [hr.1, hr.2] at r₁
    have : (s : 𝔽) * (x * v₁ + y * v₂) ^ 2 * g.f = 0 := by linear_combination -r₁
    exact (mul_ne_zero (mul_ne_zero hs0 (pow_ne_zero 2 hA)) hf) this

/-- **`lem:scalar-slice`, at most two residues.** If `G ≢ 0` and `(B, α) ≢ (0, 0)` modulo `p`,
the correction has rank at most 1 for at most two residues of `k`. -/
theorem scalar_slice [Fact p.Prime] (hp5 : 5 ≤ p) {s : ℤ} (hs : s = 1 ∨ s = 2) (g : Tern)
    (x y : ℤ) (hG : g.NonzeroMod p)
    (hBα : ¬ ((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c ∧ (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y)) :
    AtMostClasses p 2 (fun k => (g.corr s x y k).RankLeOneMod p) := by
  intro ks hlen hpair
  match ks, hlen, hpair with
  | [k₁, k₂, k₃], _, hpair =>
    obtain ⟨d12, d13, d23⟩ := three_distinct hpair
    by_contra hall
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      not_or, not_not] at hall
    obtain ⟨b₁, b₂, b₃⟩ := hall
    by_cases hB : (p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c
    · exact not_two_of_B_zero hp5 hs g x y hG hB.1 hB.2.1 hB.2.2
        (fun h => hBα ⟨hB.1, hB.2.1, hB.2.2, h⟩) d12 b₁ b₂
    · obtain ⟨v₁, v₂, hv⟩ := exists_aniso hp5 hB
      exact quad_not_three (mul_ne_zero (neg_ne_zero.mpr (s_ne_zero hp5 hs)) hv) d12 d13 d23
        (root_of_rankLe g s x y k₁ v₁ v₂ b₁) (root_of_rankLe g s x y k₂ v₁ v₂ b₂)
        (root_of_rankLe g s x y k₃ v₁ v₂ b₃)

/-- **The square case.** If `B(v, v) ≡ s A²` with `A = αᵀ v ≢ 0`, the Gram polynomial is
`-(s A k - R)²`, so at most one residue of `k` gives rank at most 1. -/
theorem not_two_of_square [Fact p.Prime] (hp5 : 5 ≤ p) {s : ℤ} (hs : s = 1 ∨ s = 2)
    (g : Tern) (x y v₁ v₂ : ℤ) (hA : ((x * v₁ + y * v₂ : ℤ) : 𝔽) ≠ 0)
    (hBv : (bnorm g v₁ v₂ : 𝔽) = s * ((x * v₁ + y * v₂ : ℤ) : 𝔽) ^ 2) {k₁ k₂ : ℤ}
    (h12 : (k₁ : 𝔽) ≠ k₂) (b₁ : (g.corr s x y k₁).RankLeOneMod p)
    (b₂ : (g.corr s x y k₂).RankLeOneMod p) : False := by
  have r₁ := root_of_rankLe g s x y k₁ v₁ v₂ b₁
  have r₂ := root_of_rankLe g s x y k₂ v₁ v₂ b₂
  rw [hBv] at r₁ r₂
  exact sq_not_two (σ := (s : 𝔽) * ((x * v₁ + y * v₂ : ℤ) : 𝔽))
    (ρ := ((g.d * v₁ + g.e * v₂ : ℤ) : 𝔽)) (mul_ne_zero (s_ne_zero hp5 hs) hA) h12
    (by linear_combination r₁) (by linear_combination r₂)

/-- `B(v, v) = B'(v, v) + s (αᵀ v)²`, and `B v = B' v + s α (αᵀ v)`. -/
theorem bnorm_split (g : Tern) (s x y v₁ v₂ : ℤ) :
    bnorm g v₁ v₂ = bnorm (g.corr s x y 0) v₁ v₂ + s * (x * v₁ + y * v₂) ^ 2 := by
  simp only [bnorm, Tern.corr]; ring

/-- **`lem:scalar-slice`, at most one residue.** If moreover `p ∤ δ`, or `B ≡ 0`, or
`B' ≡ 0 (mod p)`, the correction has rank at most 1 for at most one residue of `k`. -/
theorem scalar_slice_one [Fact p.Prime] (hp5 : 5 ≤ p) {s : ℤ} (hs : s = 1 ∨ s = 2) (g : Tern)
    (x y : ℤ) (hG : g.NonzeroMod p)
    (hBα : ¬ ((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c ∧ (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y))
    (h1 : ¬ (p : ℤ) ∣ g.delta ∨ ((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c) ∨
      ((p : ℤ) ∣ g.a - s * x * x ∧ (p : ℤ) ∣ g.b - s * x * y ∧ (p : ℤ) ∣ g.c - s * y * y)) :
    AtMostClasses p 1 (fun k => (g.corr s x y k).RankLeOneMod p) := by
  intro ks hlen hpair
  match ks, hlen, hpair with
  | [k₁, k₂], _, hpair =>
    have d12 := two_distinct hpair
    by_contra hall
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      not_or, not_not] at hall
    obtain ⟨b₁, b₂⟩ := hall
    by_cases hΔ : (p : ℤ) ∣ g.corrDelta s x y
    swap
    · exact Tern.rankGeTwoMod_corr g s x y k₁ hΔ b₁
    by_cases hB : (p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c
    · exact not_two_of_B_zero hp5 hs g x y hG hB.1 hB.2.1 hB.2.2
        (fun h => hBα ⟨hB.1, hB.2.1, hB.2.2, h⟩) d12 b₁ b₂
    -- the entries of `B' = B - s ααᵀ`
    set a' : ℤ := g.a - s * x * x
    set b' : ℤ := g.b - s * x * y
    set c' : ℤ := g.c - s * y * y
    have hB'norm : ∀ v₁ v₂ : ℤ,
        (bnorm (g.corr s x y 0) v₁ v₂ : 𝔽) = (a' * v₁ * v₁ + 2 * b' * v₁ * v₂ + c' * v₂ * v₂ : ℤ) :=
      fun v₁ v₂ => by simp only [bnorm, Tern.corr, a', b', c']
    by_cases hB' : (p : ℤ) ∣ a' ∧ (p : ℤ) ∣ b' ∧ (p : ℤ) ∣ c'
    · -- `B' ≡ 0`: `α ≢ 0`, and every `v` has `B(v, v) = s A²`
      have ha := (cast_eq_zero_iff (p := p) _).mpr hB'.1
      have hb := (cast_eq_zero_iff (p := p) _).mpr hB'.2.1
      have hc := (cast_eq_zero_iff (p := p) _).mpr hB'.2.2
      have hα : (x : 𝔽) ≠ 0 ∨ (y : 𝔽) ≠ 0 := by
        by_contra h0
        simp only [not_or, not_not] at h0
        apply hB
        refine ⟨?_, ?_, ?_⟩ <;> rw [← cast_eq_zero_iff (p := p)]
        · have : ((g.a : ℤ) : 𝔽) = (a' : 𝔽) + s * x * x := by simp [a']
          rw [this, ha, h0.1]; ring
        · have : ((g.b : ℤ) : 𝔽) = (b' : 𝔽) + s * x * y := by simp [b']
          rw [this, hb, h0.1]; ring
        · have : ((g.c : ℤ) : 𝔽) = (c' : 𝔽) + s * y * y := by simp [c']
          rw [this, hc, h0.2]; ring
      obtain ⟨v₁, v₂, hA⟩ : ∃ v₁ v₂ : ℤ, ((x * v₁ + y * v₂ : ℤ) : 𝔽) ≠ 0 := by
        rcases hα with h | h
        · exact ⟨1, 0, by push_cast; simpa using h⟩
        · exact ⟨0, 1, by push_cast; simpa using h⟩
      refine not_two_of_square hp5 hs g x y v₁ v₂ hA ?_ d12 b₁ b₂
      rw [bnorm_split g s x y, Int.cast_add, hB'norm]
      push_cast
      rw [ha, hb, hc]; ring
    · -- `p ∤ δ`: a kernel vector `v` of `B'` has `A ≢ 0`
      have hδ : ¬ (p : ℤ) ∣ g.delta := by
        rcases h1 with h | h | h
        · exact h
        · exact absurd h hB
        · exact absurd h hB'
      have hdet : ((a' * c' - b' * b' : ℤ) : 𝔽) = 0 := by
        rw [cast_eq_zero_iff]
        convert hΔ using 1
        simp only [a', b', c', Tern.corrDelta, Tern.delta]; ring
      -- the kernel vector
      obtain ⟨v₁, v₂, hv, hker₁, hker₂⟩ : ∃ v₁ v₂ : ℤ, ((v₁ : 𝔽) ≠ 0 ∨ (v₂ : 𝔽) ≠ 0) ∧
          ((a' * v₁ + b' * v₂ : ℤ) : 𝔽) = 0 ∧ ((b' * v₁ + c' * v₂ : ℤ) : 𝔽) = 0 := by
        by_cases hab : (a' : 𝔽) = 0 ∧ (b' : 𝔽) = 0
        · exact ⟨1, 0, Or.inl (by simp), by push_cast; simp [hab.1],
            by push_cast; simp [hab.2]⟩
        · refine ⟨b', -a', ?_, ?_, ?_⟩
          · by_contra h0
            simp only [not_or, not_not, Int.cast_neg, neg_eq_zero] at h0
            exact hab ⟨h0.2, h0.1⟩
          · push_cast; ring
          · push_cast at hdet ⊢; linear_combination -hdet
      have hA : ((x * v₁ + y * v₂ : ℤ) : 𝔽) ≠ 0 := by
        intro hA
        push_cast at hA hker₁ hker₂ hv
        -- then `B v = 0`, so `δ v = 0`
        have e₁ : (g.a : 𝔽) * v₁ + g.b * v₂ = 0 := by
          have : (g.a : 𝔽) * v₁ + g.b * v₂ = (a' * v₁ + b' * v₂ : 𝔽) + s * x * (x * v₁ + y * v₂) := by
            simp only [a', b']; push_cast; ring
          rw [this, hker₁, hA]; ring
        have e₂ : (g.b : 𝔽) * v₁ + g.c * v₂ = 0 := by
          have : (g.b : 𝔽) * v₁ + g.c * v₂ = (b' * v₁ + c' * v₂ : 𝔽) + s * y * (x * v₁ + y * v₂) := by
            simp only [b', c']; push_cast; ring
          rw [this, hker₂, hA]; ring
        have hδ' : (g.delta : 𝔽) ≠ 0 := fun e => hδ ((cast_eq_zero_iff _).mp e)
        have f₁ : (g.delta : 𝔽) * v₁ = 0 := by
          simp only [Tern.delta]; push_cast; linear_combination (g.c : 𝔽) * e₁ - (g.b : 𝔽) * e₂
        have f₂ : (g.delta : 𝔽) * v₂ = 0 := by
          simp only [Tern.delta]; push_cast; linear_combination (g.a : 𝔽) * e₂ - (g.b : 𝔽) * e₁
        rcases hv with h | h
        · exact h ((mul_eq_zero.mp f₁).resolve_left hδ')
        · exact h ((mul_eq_zero.mp f₂).resolve_left hδ')
      refine not_two_of_square hp5 hs g x y v₁ v₂ hA ?_ d12 b₁ b₂
      rw [bnorm_split g s x y, Int.cast_add, hB'norm]
      push_cast at hker₁ hker₂ ⊢
      linear_combination (v₁ : 𝔽) * hker₁ + (v₂ : 𝔽) * hker₂

end Slice

end KimKimOh

import KimKimOh.Reduced
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Prime.Int

/-!
# Maximal ternary lattices (§2, `eq:maximal`)

Every positive-definite ternary lattice lies in a maximal one (`exists_maximal`).

If `S` is not maximal, some `x ≢ 0 (mod p)` has `G x ≡ 0 (mod p)` and
`xᵀ G x ≡ 0 (mod p²)`. After scaling by a unit modulo `p` and adding a multiple of `p eₖ`,
we may take `xₖ = 1` (`normalize_violation`). The lattice spanned by the basis with `eₖ`
replaced by `x / p` is integral, with Gram matrix `enlargeGram`, and contains `S`; its
determinant is `det G / p²` (`enlarge_eq`). Induction on the determinant finishes the
proof.

`exists_maximal_reduced` combines this with `exists_reduced`.
-/

namespace KimKimOh

open Matrix GramLattice

/-- The Gram matrix of the basis `eᵢ (i ≠ k), x / p`. -/
def enlargeGram (G : Matrix (Fin 3) (Fin 3) ℤ) (p : ℤ) (k : Fin 3) (x : Fin 3 → ℤ) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => if i = k ∧ j = k then (x ⬝ᵥ G *ᵥ x) / p ^ 2
    else if j = k then (G *ᵥ x) i / p
    else if i = k then (G *ᵥ x) j / p
    else G i j

/-- The coordinates of the old basis in the new one: `eₖ = p (x/p) - Σ_{i ≠ k} xᵢ eᵢ`. -/
def enlargeM (p : ℤ) (k : Fin 3) (x : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => if j = k then (if i = k then p else -x i) else (if i = j then 1 else 0)

theorem det_enlargeM (p : ℤ) (k : Fin 3) (x : Fin 3 → ℤ) : (enlargeM p k x).det = p := by
  fin_cases k <;> simp [enlargeM, det_fin_three]

theorem enlarge_eq (G : Matrix (Fin 3) (Fin 3) ℤ) (hsym : ∀ i j, G i j = G j i) {p : ℤ}
    (hp : p ≠ 0) (k : Fin 3) (x : Fin 3 → ℤ) (hxk : x k = 1)
    (hGx : ∀ i, p ∣ (G *ᵥ x) i) (hQ : p ^ 2 ∣ x ⬝ᵥ G *ᵥ x) :
    (enlargeM p k x)ᵀ * enlargeGram G p k x * enlargeM p k x = G := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hp2 : ((p ^ 2 : ℤ) : ℚ) ≠ 0 := by push_cast; exact pow_ne_zero 2 hp'
  have hE (i j : Fin 3) : ((enlargeGram G p k x i j : ℤ) : ℚ) =
      if i = k ∧ j = k then ((x ⬝ᵥ G *ᵥ x : ℤ) : ℚ) / (p : ℚ) ^ 2
      else if j = k then (((G *ᵥ x) i : ℤ) : ℚ) / p
      else if i = k then (((G *ᵥ x) j : ℤ) : ℚ) / p
      else (G i j : ℚ) := by
    unfold enlargeGram
    split_ifs
    · rw [Int.cast_div hQ hp2]; push_cast; rfl
    · exact Int.cast_div (hGx i) hp'
    · exact Int.cast_div (hGx j) hp'
    · rfl
  have h10 := hsym 1 0
  have h20 := hsym 2 0
  have h21 := hsym 2 1
  ext i j
  apply Int.cast_injective (α := ℚ)
  simp only [Matrix.mul_apply, transpose_apply, Int.cast_sum, Int.cast_mul, hE]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hxk <;>
    fin_cases i <;> fin_cases j <;>
    simp [enlargeM, Fin.sum_univ_three, dotProduct, mulVec, hxk, h10, h20, h21] <;>
    field_simp <;> ring

/-- A violation of maximality can be normalized to have `k`-th coordinate `1`. -/
theorem normalize_violation (G : Matrix (Fin 3) (Fin 3) ℤ) (hsym : ∀ i j, G i j = G j i)
    {p : ℕ} (hp : p.Prime) (x : Fin 3 → ℤ) (k : Fin 3) (hxk : ¬ (p : ℤ) ∣ x k)
    (hGx : ∀ i, (p : ℤ) ∣ (G *ᵥ x) i) (hQ : (p : ℤ) ^ 2 ∣ x ⬝ᵥ G *ᵥ x) :
    ∃ y : Fin 3 → ℤ, y k = 1 ∧ (∀ i, (p : ℤ) ∣ (G *ᵥ y) i) ∧
      (p : ℤ) ^ 2 ∣ y ⬝ᵥ G *ᵥ y := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, u, hau⟩ := (Prime.coprime_iff_not_dvd hpZ).mpr hxk
  set c : ℤ := p * a
  refine ⟨u • x + c • Pi.single k 1, ?_, ?_, ?_⟩
  · simp [c]; linear_combination hau
  · intro i
    rw [mulVec_add, mulVec_smul, mulVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact dvd_add (dvd_mul_of_dvd_right (hGx i) _) (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  · have hexp : (u • x + c • Pi.single k 1) ⬝ᵥ G *ᵥ (u • x + c • Pi.single k 1) =
        u ^ 2 * (x ⬝ᵥ G *ᵥ x) + 2 * u * c * (G *ᵥ x) k + c ^ 2 * G k k := by
      have h10 := hsym 1 0
      have h20 := hsym 2 0
      have h21 := hsym 2 1
      fin_cases k <;> simp [dotProduct, mulVec, Fin.sum_univ_three, h10, h20, h21] <;> ring
    rw [hexp]
    obtain ⟨q, hq⟩ := hGx k
    obtain ⟨r, hr⟩ := hQ
    exact ⟨u ^ 2 * r + 2 * u * a * q + a ^ 2 * G k k, by rw [hr, hq]; ring⟩

/-- One enlargement step: a non-maximal ternary lattice lies in one of smaller
determinant. -/
theorem exists_enlargement (S : GramLattice (Fin 3)) (h : ¬ IsMaximal S.gram) :
    ∃ S' : GramLattice (Fin 3), S'.Represents S ∧ S'.gram.det < S.gram.det := by
  simp only [IsMaximal, not_forall, not_not] at h
  obtain ⟨p, hp, x, ⟨k, hk⟩, hGx, hQ⟩ := h
  have hsym (i j : Fin 3) : S.gram i j = S.gram j i := S.gram_comm i j
  obtain ⟨y, hyk, hGy, hQy⟩ := normalize_violation S.gram hsym hp x k hk hGx hQ
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have heq := enlarge_eq S.gram hsym hp0 k y hyk hGy hQy
  set M := enlargeM (p : ℤ) k y
  set G₁ := enlargeGram S.gram (p : ℤ) k y
  have hMdet : M.det = p := det_enlargeM _ k y
  -- `G₁` is positive definite since `Mᵀ G₁ M = G`, and the determinant drops by a factor `p²`
  have hpos : (G₁.map (Int.cast : ℤ → ℝ)).PosDef :=
    S.posDef_of_pullback (by rw [hMdet]; exact hp0) heq
  refine ⟨⟨G₁, hpos⟩, ⟨M, heq⟩, ?_⟩
  have hdet : S.gram.det = p ^ 2 * G₁.det := by
    rw [← heq, det_mul, det_mul, det_transpose, hMdet]; ring
  have hG₁pos : 0 < G₁.det := GramLattice.gram_det_pos ⟨G₁, hpos⟩
  have hp2 : (4 : ℤ) ≤ (p : ℤ) ^ 2 := by
    have := hp.two_le
    have : (2 : ℤ) ≤ p := by exact_mod_cast this
    nlinarith
  change G₁.det < S.gram.det
  rw [hdet]
  nlinarith

/-- **Maximal enlargements.** Every positive-definite ternary lattice lies in a maximal
one. -/
theorem exists_maximal (S : GramLattice (Fin 3)) :
    ∃ S' : GramLattice (Fin 3), IsMaximal S'.gram ∧ S'.Represents S := by
  induction h : S.gram.det.toNat using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hmax : IsMaximal S.gram
    · exact ⟨S, hmax, Represents.refl S⟩
    · obtain ⟨S₁, hS₁, hdet⟩ := exists_enlargement S hmax
      have hpos : 0 < S₁.gram.det := S₁.gram_det_pos
      obtain ⟨S', hS', hS'₁⟩ := ih S₁.gram.det.toNat (by omega) S₁ rfl
      exact ⟨S', hS', hS'₁.trans hS₁⟩

/-- Every ternary lattice lies in a maximal ternary lattice, which has a reduced basis. -/
theorem exists_maximal_reduced (S : GramLattice (Fin 3)) :
    ∃ S' : GramLattice (Fin 3), IsMaximal S'.gram ∧ (ternOf S').IsReduced ∧ S'.Represents S := by
  obtain ⟨S₁, hmax, hS₁⟩ := exists_maximal S
  obtain ⟨W, hW, hred⟩ := exists_reduced S₁
  exact ⟨S₁.conj W hW, isMaximal_conj hmax W hW, hred, (conj_represents S₁ W hW).trans hS₁⟩

end KimKimOh

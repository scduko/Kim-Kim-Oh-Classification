import KimKimOh.GramLattice.Isometry
import KimKimOh.Maximal
import KimKimOh.Ternary
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination

/-!
# Reduced bases of ternary lattices (§3)

Every positive-definite ternary lattice has a basis whose Gram matrix satisfies
`Tern.IsReduced` (`exists_reduced`): the inequalities of §3 (`eq:lengths`) of a size-reduced
Korkine–Zolotarev basis. The basis is found as follows.

* Among all bases, take one minimizing `(a, δ)` lexicographically, where `a = Q(v₁)` and
  `δ = Q(v₁)Q(v₂) - (v₁, v₂)²` (`exists_isMinimal`). Then `a` is the minimum of the
  lattice, because a primitive vector extends to a basis (`exists_unimodular_col`), and
  `δ ≤ af - d²`, because `v₂` and `v₃` can be exchanged.
* The size-reducing change of basis (`sizeMatrix`) changes neither `a` nor `δ`, so the result
  is again minimal, and it gives `0 ≤ 2b ≤ a`, `2|d| ≤ a` and `2|ae - bd| ≤ δ`
  (`exists_round`).
* The identity `δ(af - d²) = aD + (ae - bd)²` then gives `3δ² ≤ 4aD`, that is
  `γ ≥ 3β/4`.

A change of basis is `GramLattice.conj S W` (`GramLattice/Isometry.lean`), with Gram matrix
`Wᵀ G W` for a unimodular `W`; it preserves maximality (`isMaximal_conj`). `ternOf S` is the ternary `Tern` of entries of a Gram matrix, with
`a, δ, D > 0` (`a_pos`, `delta_pos`, `det_pos`).
-/

namespace KimKimOh

open Matrix

/-! ### Change of basis -/

namespace GramLattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isUnit_det_mul {W V : Matrix ι ι ℤ} (hW : IsUnit W.det) (hV : IsUnit V.det) :
    IsUnit (W * V).det := by
  rw [det_mul]; exact hW.mul hV

theorem conj_conj (S : GramLattice ι) (W V : Matrix ι ι ℤ) (hW : IsUnit W.det)
    (hV : IsUnit V.det) :
    (S.conj W hW).conj V hV = S.conj (W * V) (isUnit_det_mul hW hV) :=
  ext (by simp only [conj_gram, transpose_mul, Matrix.mul_assoc])

end GramLattice

/-! ### Maximality is preserved by a change of basis -/

theorem dvd_mulVec_of_dvd {ι : Type*} [Fintype ι] (A : Matrix ι ι ℤ) {v : ι → ℤ} {n : ℤ}
    (h : ∀ i, n ∣ v i) (i : ι) : n ∣ (A *ᵥ v) i :=
  Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (h j) _

/-- Maximality does not depend on the basis. -/
theorem isMaximal_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℤ}
    (hG : IsMaximal G) (W : Matrix ι ι ℤ) (hW : IsUnit W.det) : IsMaximal (Wᵀ * G * W) := by
  intro p hp x hx hGx hQ
  refine hG p hp (W *ᵥ x) ?_ ?_ ?_
  · obtain ⟨i, hi⟩ := hx
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hi
    have h := dvd_mulVec_of_dvd W⁻¹ hall i
    rwa [mulVec_mulVec, nonsing_inv_mul _ hW, one_mulVec] at h
  · intro i
    have h := dvd_mulVec_of_dvd (W⁻¹)ᵀ hGx i
    have key : (W⁻¹)ᵀ *ᵥ ((Wᵀ * G * W) *ᵥ x) = G *ᵥ (W *ᵥ x) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← transpose_mul, mul_nonsing_inv _ hW, transpose_one, Matrix.one_mul]
    rwa [key] at h
  · have key : x ⬝ᵥ (Wᵀ * G * W) *ᵥ x = (W *ᵥ x) ⬝ᵥ G *ᵥ (W *ᵥ x) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rwa [key] at hQ

open GramLattice

/-! ### The entries of a ternary lattice -/

/-- The entries `(a, b, c, d, e, f)` of a ternary lattice. -/
abbrev ternOf (S : GramLattice (Fin 3)) : Tern := Tern.ofMatrix S.gram

theorem a_pos (S : GramLattice (Fin 3)) : 0 < (ternOf S).a := by
  have h0 : (0 : ℝ) < (S.gram 0 0 : ℝ) := by simpa using S.posDef.diag_pos (i := 0)
  exact_mod_cast h0

theorem delta_pos (S : GramLattice (Fin 3)) : 0 < (ternOf S).delta := by
  have h := (S.posDef.submatrix (e := (Fin.castSucc : Fin 2 → Fin 3))
    (Fin.castSucc_injective 2)).det_pos
  rw [det_fin_two] at h
  simp only [submatrix_apply, map_apply] at h
  have hs := S.gram_comm 1 0
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h
  have : (0 : ℝ) < ((S.gram 0 0 * S.gram 1 1 - S.gram 0 1 * S.gram 0 1 : ℤ) : ℝ) := by
    push_cast; rw [hs] at h; exact h
  exact_mod_cast this

theorem ternOf_toMatrix (S : GramLattice (Fin 3)) : (ternOf S).toMatrix = S.gram :=
  Tern.toMatrix_ofMatrix S.gram_isSymm

theorem ternOf_det (S : GramLattice (Fin 3)) : (ternOf S).det = S.gram.det := by
  rw [← Tern.det_toMatrix, ternOf_toMatrix]

theorem det_pos (S : GramLattice (Fin 3)) : 0 < (ternOf S).det := by
  rw [ternOf_det]; exact S.gram_det_pos

/-- The value `vᵀ G v` agrees with `Tern.eval`. -/
theorem eval_ternOf (S : GramLattice (Fin 3)) (x y z : ℤ) :
    (ternOf S).eval x y z = ![x, y, z] ⬝ᵥ S.gram *ᵥ ![x, y, z] := by
  have h10 := S.gram_comm 1 0
  have h20 := S.gram_comm 2 0
  have h21 := S.gram_comm 2 1
  simp [Tern.eval, Tern.ofMatrix, dotProduct, mulVec, Fin.sum_univ_three, h10, h20, h21]
  ring

/-! ### Minimal bases -/

/-- `S` minimizes `(a, δ)` lexicographically among all bases of its lattice. -/
def IsMinimal (S : GramLattice (Fin 3)) : Prop :=
  ∀ (V : Matrix (Fin 3) (Fin 3) ℤ) (hV : IsUnit V.det),
    (ternOf S).a ≤ (ternOf (S.conj V hV)).a ∧
      ((ternOf S).a = (ternOf (S.conj V hV)).a →
        (ternOf S).delta ≤ (ternOf (S.conj V hV)).delta)

theorem isUnit_det_one : IsUnit (1 : Matrix (Fin 3) (Fin 3) ℤ).det := by simp

theorem conj_one (S : GramLattice (Fin 3)) : S.conj 1 isUnit_det_one = S :=
  GramLattice.ext (by simp)

theorem exists_isMinimal (S : GramLattice (Fin 3)) :
    ∃ (W : Matrix (Fin 3) (Fin 3) ℤ) (hW : IsUnit W.det), IsMinimal (S.conj W hW) := by
  classical
  have hA : ∃ n : ℕ, ∃ (W : Matrix (Fin 3) (Fin 3) ℤ) (hW : IsUnit W.det),
      (ternOf (S.conj W hW)).a = n :=
    ⟨(ternOf S).a.toNat, 1, isUnit_det_one, by
      rw [conj_one]; exact (Int.toNat_of_nonneg (a_pos S).le).symm⟩
  obtain ⟨W₀, hW₀, ha₀⟩ := Nat.find_spec hA
  have hB : ∃ m : ℕ, ∃ (W : Matrix (Fin 3) (Fin 3) ℤ) (hW : IsUnit W.det),
      (ternOf (S.conj W hW)).a = Nat.find hA ∧ (ternOf (S.conj W hW)).delta = m :=
    ⟨(ternOf (S.conj W₀ hW₀)).delta.toNat, W₀, hW₀, ha₀,
      (Int.toNat_of_nonneg (delta_pos _).le).symm⟩
  obtain ⟨W₁, hW₁, ha₁, hd₁⟩ := Nat.find_spec hB
  refine ⟨W₁, hW₁, fun V hV => ?_⟩
  rw [conj_conj]
  set T := S.conj (W₁ * V) (isUnit_det_mul hW₁ hV)
  have hTa : (ternOf T).a = ((ternOf T).a.toNat : ℤ) :=
    (Int.toNat_of_nonneg (a_pos T).le).symm
  have hmin : Nat.find hA ≤ (ternOf T).a.toNat :=
    Nat.find_min' hA ⟨W₁ * V, isUnit_det_mul hW₁ hV, hTa⟩
  refine ⟨by rw [ha₁, hTa]; exact_mod_cast hmin, fun heq => ?_⟩
  have hTd : (ternOf T).delta = ((ternOf T).delta.toNat : ℤ) :=
    (Int.toNat_of_nonneg (delta_pos T).le).symm
  have hmin' : Nat.find hB ≤ (ternOf T).delta.toNat :=
    Nat.find_min' hB ⟨W₁ * V, isUnit_det_mul hW₁ hV, heq ▸ ha₁, hTd⟩
  rw [hd₁, hTd]; exact_mod_cast hmin'

/-! ### Completing a primitive vector to a basis -/

/-- Every nonzero `v ∈ ℤ³` is a nonzero multiple of the first column of a unimodular
matrix. -/
theorem exists_unimodular_col (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    ∃ W : Matrix (Fin 3) (Fin 3) ℤ, IsUnit W.det ∧ ∃ g : ℤ, g ≠ 0 ∧ ∀ i, v i = g * W i 0 := by
  by_cases h01 : Int.gcd (v 0) (v 1) = 0
  · obtain ⟨h0, h1⟩ := Int.gcd_eq_zero_iff.mp h01
    have h2 : v 2 ≠ 0 := by
      intro h2; apply hv; funext i; fin_cases i <;> simp [h0, h1, h2]
    refine ⟨Matrix.of ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]], ?_, v 2, h2, ?_⟩
    · rw [det_fin_three]; simp
    · intro i; fin_cases i <;> simp [h0, h1]
  · set g₁ : ℤ := ((Int.gcd (v 0) (v 1) : ℕ) : ℤ) with hg₁
    have hg₁0 : g₁ ≠ 0 := by simpa [hg₁] using h01
    obtain ⟨x', hx'⟩ : g₁ ∣ v 0 := Int.gcd_dvd_left _ _
    obtain ⟨y', hy'⟩ : g₁ ∣ v 1 := Int.gcd_dvd_right _ _
    have hbez₁ : g₁ = v 0 * Int.gcdA (v 0) (v 1) + v 1 * Int.gcdB (v 0) (v 1) :=
      Int.gcd_eq_gcd_ab _ _
    have hxy : x' * Int.gcdA (v 0) (v 1) + y' * Int.gcdB (v 0) (v 1) = 1 := by
      apply mul_left_cancel₀ hg₁0
      linear_combination -hbez₁ - Int.gcdA (v 0) (v 1) * hx' - Int.gcdB (v 0) (v 1) * hy'
    set g : ℤ := ((Int.gcd g₁ (v 2) : ℕ) : ℤ) with hg
    have hg0 : g ≠ 0 := by
      intro h; apply hg₁0
      rw [hg] at h
      exact (Int.gcd_eq_zero_iff.mp (Int.natCast_eq_zero.mp h)).1
    obtain ⟨g₁', hg₁'⟩ : g ∣ g₁ := Int.gcd_dvd_left _ _
    obtain ⟨z', hz'⟩ : g ∣ v 2 := Int.gcd_dvd_right _ _
    have hbez : g = g₁ * Int.gcdA g₁ (v 2) + v 2 * Int.gcdB g₁ (v 2) := Int.gcd_eq_gcd_ab _ _
    have hgz : g₁' * Int.gcdA g₁ (v 2) + z' * Int.gcdB g₁ (v 2) = 1 := by
      apply mul_left_cancel₀ hg0
      linear_combination -hbez - Int.gcdA g₁ (v 2) * hg₁' - Int.gcdB g₁ (v 2) * hz'
    set u := Int.gcdA (v 0) (v 1)
    set w := Int.gcdB (v 0) (v 1)
    set s := Int.gcdA g₁ (v 2)
    set t := Int.gcdB g₁ (v 2)
    refine ⟨Matrix.of ![![x', -w, 0], ![y', u, 0], ![0, 0, 1]] *
      Matrix.of ![![g₁', 0, -t], ![0, 1, 0], ![z', 0, s]], ?_, g, hg0, ?_⟩
    · have hC : (Matrix.of ![![x', -w, 0], ![y', u, 0], ![0, 0, 1]]).det = 1 := by
        simp [det_fin_three]; linear_combination hxy
      have hB : (Matrix.of ![![g₁', 0, -t], ![0, 1, 0], ![z', 0, s]]).det = 1 := by
        simp [det_fin_three]; linear_combination hgz
      rw [det_mul, hC, hB]; exact isUnit_one
    · intro i
      fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      · rw [hx', hg₁']; ring
      · rw [hy', hg₁']; ring
      · rw [hz']

/-- In a minimal basis, `a` is the minimum of the lattice. -/
theorem IsMinimal.a_le (S : GramLattice (Fin 3)) (hS : IsMinimal S) (v : Fin 3 → ℤ)
    (hv : v ≠ 0) : (ternOf S).a ≤ v ⬝ᵥ S.gram *ᵥ v := by
  obtain ⟨W, hW, g, hg, hvW⟩ := exists_unimodular_col v hv
  have h := (hS W hW).1
  set w : Fin 3 → ℤ := fun i => W i 0
  have hQw : (ternOf (S.conj W hW)).a = w ⬝ᵥ S.gram *ᵥ w := by
    simp [ternOf, Tern.ofMatrix, conj, Matrix.mul_apply, dotProduct, mulVec, w,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hv' : v = g • w := by funext i; simp [hvW i, w]
  have hQv : v ⬝ᵥ S.gram *ᵥ v = g ^ 2 * (w ⬝ᵥ S.gram *ᵥ w) := by
    rw [hv', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hpos : 0 ≤ w ⬝ᵥ S.gram *ᵥ w := by rw [← hQw]; exact (a_pos _).le
  have hg2 : 1 ≤ g ^ 2 := by
    have := sq_pos_of_ne_zero hg
    omega
  rw [hQv]
  nlinarith

/-! ### Size reduction -/

/-- **Centring a progression.** For `A, h > 0`, any `B` and any class `ρ` modulo `h`, some
`x₀ ≡ ρ (mod h)` has `|2A(x₀ + h t) - B| ≤ A h m` for all `t < m`: the `m` terms `x₀ + h t`
lie within `h m / 2` of `B / (2A)`. -/
theorem exists_centred_progression {A B h : ℤ} (hA : 0 < A) (hh : 0 < h) (ρ : ℤ) (m : ℕ) :
    ∃ x₀ : ℤ, h ∣ x₀ - ρ ∧ ∀ t : ℕ, t < m → |2 * A * (x₀ + h * t) - B| ≤ A * h * m := by
  set W := A * h with hW
  have hW0 : 0 < W := mul_pos hA hh
  set u := B - W * m - 2 * A * ρ
  set q := -((-u) / (2 * W))
  have h1 := Int.emod_add_mul_ediv (-u) (2 * W)
  have h2 := Int.emod_nonneg (-u) (by omega : 2 * W ≠ 0)
  have h3 := Int.emod_lt_of_pos (-u) (by omega : 0 < 2 * W)
  have hq1 : u ≤ 2 * W * q := by simp only [q]; linarith
  have hq2 : 2 * W * q < u + 2 * W := by simp only [q]; linarith
  refine ⟨ρ + h * q, ⟨q, by ring⟩, fun t ht => ?_⟩
  have ht' : (t : ℤ) + 1 ≤ m := by exact_mod_cast ht
  have e : 2 * A * (ρ + h * q + h * t) - B = 2 * W * q + 2 * W * t - (u + W * m) := by
    simp only [hW, u]; ring
  rw [e, abs_le]
  have hWt : 0 ≤ W * t := mul_nonneg hW0.le (by positivity)
  have hWt' : W * (t + 1) ≤ W * m := mul_le_mul_of_nonneg_left ht' hW0.le
  constructor <;> nlinarith

/-- Some multiple of `q > 0` lies within `q / 2` of `n`. -/
theorem exists_round (n q : ℤ) (hq : 0 < q) : ∃ k : ℤ, 2 * |n - k * q| ≤ q := by
  obtain ⟨x₀, ⟨k, hk⟩, h⟩ := exists_centred_progression (B := 2 * n) one_pos hq 0 1
  refine ⟨k, ?_⟩
  have := h 0 one_pos
  rw [sub_zero] at hk
  rw [hk, show 2 * 1 * (q * k + q * ((0 : ℕ) : ℤ)) - 2 * n = -(2 * (n - k * q)) by push_cast; ring,
    abs_neg, abs_mul, abs_two] at this
  simpa using this

/-- The size-reducing change of basis `(v₁, σ(v₂ - m v₁), v₃ - k v₂ - l v₁)`. -/
def sizeMatrix (σ m k l : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![![1, -σ * m, -l], ![0, σ, -k], ![0, 0, 1]]

theorem det_sizeMatrix (σ m k l : ℤ) : (sizeMatrix σ m k l).det = σ := by
  rw [det_fin_three]; simp [sizeMatrix]

theorem sizeMatrix_entries (S : GramLattice (Fin 3)) (σ m k l : ℤ)
    (hV : IsUnit (sizeMatrix σ m k l).det) (hσ : σ * σ = 1) :
    let g := ternOf S
    let T := ternOf (S.conj (sizeMatrix σ m k l) hV)
    T.a = g.a ∧ T.b = σ * (g.b - m * g.a) ∧ T.c = g.c - 2 * m * g.b + m * m * g.a ∧
      T.d = g.d - k * g.b - l * g.a ∧
      T.e = σ * ((g.e - k * g.c - l * g.b) - m * (g.d - k * g.b - l * g.a)) ∧
      T.delta = g.delta ∧
      g.a * T.e - T.b * T.d = σ * ((g.a * g.e - g.b * g.d) - k * g.delta) := by
  intro g T
  have h10 := S.gram_comm 1 0
  have h20 := S.gram_comm 2 0
  have h21 := S.gram_comm 2 1
  have ha : T.a = g.a := by
    simp [T, g, Tern.ofMatrix, conj, sizeMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  have hb : T.b = σ * (g.b - m * g.a) := by
    simp [T, g, Tern.ofMatrix, conj, sizeMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      h10]
    ring
  have hc : T.c = g.c - 2 * m * g.b + m * m * g.a := by
    simp [T, g, Tern.ofMatrix, conj, sizeMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      h10]
    linear_combination (S.gram 1 1 - 2 * m * S.gram 0 1 + m * m * S.gram 0 0) * hσ
  have hd : T.d = g.d - k * g.b - l * g.a := by
    simp [T, g, Tern.ofMatrix, conj, sizeMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      h10, h20]
    ring
  have he : T.e = σ * ((g.e - k * g.c - l * g.b) - m * (g.d - k * g.b - l * g.a)) := by
    simp [T, g, Tern.ofMatrix, conj, sizeMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      h10, h20, h21]
    ring
  refine ⟨ha, hb, hc, hd, he, ?_, ?_⟩
  · simp only [Tern.delta, ha, hb, hc]
    linear_combination -(g.b - m * g.a) ^ 2 * hσ
  · rw [he, hb, hd]; simp only [Tern.delta]; ring

theorem delta_mul_proj (g : Tern) :
    g.delta * (g.a * g.f - g.d * g.d) = g.a * g.det + (g.a * g.e - g.b * g.d) ^ 2 := by
  simp only [Tern.delta, Tern.det]; ring

/-- The exchange of the second and third basis vectors. -/
def swap23 : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of ![![1, 0, 0], ![0, 0, 1], ![0, 1, 0]]

theorem isUnit_det_swap23 : IsUnit swap23.det := by
  rw [show swap23.det = -1 by simp [swap23, det_fin_three]]; exact isUnit_one.neg

/-- **Reduced bases.** Every positive-definite ternary lattice has a basis whose Gram matrix
satisfies the inequalities of §3 (`eq:lengths`) of a size-reduced Korkine–Zolotarev basis. -/
theorem exists_reduced (S : GramLattice (Fin 3)) :
    ∃ (W : Matrix (Fin 3) (Fin 3) ℤ) (hW : IsUnit W.det), (ternOf (S.conj W hW)).IsReduced := by
  obtain ⟨W₀, hW₀, hmin⟩ := exists_isMinimal S
  set T := S.conj W₀ hW₀
  set g := ternOf T with hg
  have ha := a_pos T
  have hδ := delta_pos T
  obtain ⟨k, hk⟩ := exists_round (g.a * g.e - g.b * g.d) g.delta hδ
  obtain ⟨l, hl⟩ := exists_round (g.d - k * g.b) g.a ha
  obtain ⟨m, hm⟩ := exists_round g.b g.a ha
  obtain ⟨σ, hσ, hσb, habs, hσu⟩ : ∃ σ : ℤ, σ * σ = 1 ∧ 0 ≤ σ * (g.b - m * g.a) ∧
      (∀ x : ℤ, |σ * x| = |x|) ∧ IsUnit σ := by
    rcases le_or_gt 0 (g.b - m * g.a) with h | h
    · exact ⟨1, by norm_num, by linarith, fun x => by simp, isUnit_one⟩
    · exact ⟨-1, by norm_num, by linarith, fun x => by simp, isUnit_one.neg⟩
  have hV : IsUnit (sizeMatrix σ m k l).det := by
    rw [det_sizeMatrix]; exact hσu
  refine ⟨W₀ * sizeMatrix σ m k l, isUnit_det_mul hW₀ hV, ?_⟩
  rw [← conj_conj S W₀ (sizeMatrix σ m k l) hW₀ hV]
  set R := T.conj (sizeMatrix σ m k l) hV
  obtain ⟨hRa, hRb, -, hRd, -, hRδ, hRμ⟩ := sizeMatrix_entries T σ m k l hV hσ
  change (ternOf R).a = g.a at hRa
  change (ternOf R).b = σ * (g.b - m * g.a) at hRb
  change (ternOf R).d = g.d - k * g.b - l * g.a at hRd
  change (ternOf R).delta = g.delta at hRδ
  change g.a * (ternOf R).e - (ternOf R).b * (ternOf R).d =
    σ * ((g.a * g.e - g.b * g.d) - k * g.delta) at hRμ
  have hRmin : IsMinimal R := by
    intro V hV'
    rw [conj_conj]
    have h := hmin (sizeMatrix σ m k l * V) (isUnit_det_mul hV hV')
    rw [hRa, hRδ]
    exact h
  have hle : ∀ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) → (ternOf R).a ≤ (ternOf R).eval x y z := by
    intro x y z hxyz
    rw [eval_ternOf]
    refine IsMinimal.a_le R hRmin ![x, y, z] ?_
    intro h0
    apply hxyz
    have h0' := congrFun h0 0
    have h1' := congrFun h0 1
    have h2' := congrFun h0 2
    simp at h0' h1' h2'
    simp [h0', h1', h2']
  have hc : (ternOf R).a ≤ (ternOf R).c := by
    have := hle 0 1 0 (by simp); simpa [Tern.eval] using this
  have hf : (ternOf R).a ≤ (ternOf R).f := by
    have := hle 0 0 1 (by simp); simpa [Tern.eval] using this
  have hproj : (ternOf R).delta ≤ (ternOf R).a * (ternOf R).f - (ternOf R).d * (ternOf R).d := by
    have h := hRmin swap23 isUnit_det_swap23
    have hsa : (ternOf (R.conj swap23 isUnit_det_swap23)).a = (ternOf R).a := by
      simp [ternOf, Tern.ofMatrix, conj, swap23, Matrix.mul_apply, Fin.sum_univ_three]
    have hsd : (ternOf (R.conj swap23 isUnit_det_swap23)).delta =
        (ternOf R).a * (ternOf R).f - (ternOf R).d * (ternOf R).d := by
      have h20 := R.gram_comm 2 0
      simp [ternOf, Tern.ofMatrix, Tern.delta, conj, swap23, Matrix.mul_apply,
        Fin.sum_univ_three, h20]
    rw [← hsd]
    exact h.2 hsa.symm
  have hμ : 2 * |(ternOf R).a * (ternOf R).e - (ternOf R).b * (ternOf R).d| ≤ (ternOf R).delta := by
    rw [hRa, hRμ, habs, hRδ]; exact hk
  refine
    { b_nonneg := by rw [hRb]; exact hσb
      two_b_le_a := by
        rw [hRb, hRa]
        have := le_abs_self (σ * (g.b - m * g.a))
        rw [habs] at this
        linarith
      a_le_c := hc
      two_d_le := by rw [hRd, hRa]; exact hl
      two_mu_le := hμ
      a_le_f := hf
      delta_le_proj := hproj
      height := by
        have hid := delta_mul_proj (ternOf R)
        have hδR : 0 < (ternOf R).delta := by rw [hRδ]; exact hδ
        set μ := (ternOf R).a * (ternOf R).e - (ternOf R).b * (ternOf R).d
        have h4 : 4 * μ ^ 2 ≤ (ternOf R).delta ^ 2 := by
          have h0 : 0 ≤ 2 * |μ| := by positivity
          have : (2 * |μ|) ^ 2 ≤ (ternOf R).delta ^ 2 := pow_le_pow_left₀ h0 hμ 2
          rw [mul_pow, sq_abs] at this
          linarith
        nlinarith
      a_le_eval := hle }

end KimKimOh

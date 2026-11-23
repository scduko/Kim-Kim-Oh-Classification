import KimKimOh.GramLattice

/-!
# Isometry, the bilinear form, and pullbacks

General notions for lattices given by Gram matrices.

* `GramLattice.Isometric L M`: some `X` with `Xᵀ G_L X = G_M` has an integral right inverse, so
  the columns of `X` form a basis of `L`. It is an equivalence relation and preserves
  representations both ways (`Isometric.represents_iff`, `Isometric.isUniversal_iff`).
* `GramLattice.bf L u v = uᵀ G_L v` and its values; `qf_pos`: nonzero integer vectors have
  positive norm.
* `posDef_pullback_int`: `Bᵀ G B` is positive definite as soon as `B` is injective on integer
  vectors (no real injectivity is needed).
* `GramLattice.ofPullback`: the lattice with Gram matrix `Bᵀ G_L B`; `GramLattice.conj`, a change
  of basis by a unimodular matrix.
-/

namespace KimKimOh

open Matrix

variable {ι κ μ : Type*} [Fintype ι]

namespace GramLattice

/-! ### The bilinear form -/

/-- The pairing `uᵀ G v` of two integer vectors. -/
def bf (L : GramLattice ι) (u v : ι → ℤ) : ℤ := u ⬝ᵥ (L.gram *ᵥ v)

/-- The norm `vᵀ G v`. -/
def qf (L : GramLattice ι) (v : ι → ℤ) : ℤ := L.bf v v

theorem bf_comm (L : GramLattice ι) (u v : ι → ℤ) : L.bf u v = L.bf v u := by
  unfold bf
  rw [dotProduct_mulVec, ← mulVec_transpose, L.gram_isSymm.eq, dotProduct_comm]

theorem bf_add_left (L : GramLattice ι) (u u' v : ι → ℤ) :
    L.bf (u + u') v = L.bf u v + L.bf u' v := by
  simp [bf, add_dotProduct]

theorem bf_add_right (L : GramLattice ι) (u v v' : ι → ℤ) :
    L.bf u (v + v') = L.bf u v + L.bf u v' := by
  simp [bf, mulVec_add, dotProduct_add]

theorem bf_smul_left (L : GramLattice ι) (c : ℤ) (u v : ι → ℤ) :
    L.bf (c • u) v = c * L.bf u v := by
  rw [bf, smul_dotProduct, smul_eq_mul, bf]

theorem bf_smul_right (L : GramLattice ι) (c : ℤ) (u v : ι → ℤ) :
    L.bf u (c • v) = c * L.bf u v := by
  rw [bf, mulVec_smul, dotProduct_smul, smul_eq_mul, bf]

theorem bf_neg_left (L : GramLattice ι) (u v : ι → ℤ) : L.bf (-u) v = -L.bf u v := by
  simp [bf, neg_dotProduct]

theorem bf_neg_right (L : GramLattice ι) (u v : ι → ℤ) : L.bf u (-v) = -L.bf u v := by
  simp [bf, mulVec_neg, dotProduct_neg]

theorem bf_sub_left (L : GramLattice ι) (u u' v : ι → ℤ) :
    L.bf (u - u') v = L.bf u v - L.bf u' v := by
  simp [bf, sub_dotProduct]

theorem bf_sub_right (L : GramLattice ι) (u v v' : ι → ℤ) :
    L.bf u (v - v') = L.bf u v - L.bf u v' := by
  simp [bf, mulVec_sub, dotProduct_sub]

theorem bf_zero_left (L : GramLattice ι) (v : ι → ℤ) : L.bf 0 v = 0 := by simp [bf]

theorem bf_zero_right (L : GramLattice ι) (u : ι → ℤ) : L.bf u 0 = 0 := by simp [bf]

/-- The norm of a nonzero vector is positive. -/
theorem qf_pos (L : GramLattice ι) {v : ι → ℤ} (hv : v ≠ 0) : 0 < L.qf v := by
  have hv' : (fun i => (v i : ℝ)) ≠ 0 := by
    intro h
    apply hv
    funext i
    simpa using congrFun h i
  have h := L.posDef.dotProduct_mulVec_pos hv'
  have e : star (fun i => (v i : ℝ)) ⬝ᵥ (L.gram.map (Int.cast : ℤ → ℝ) *ᵥ fun i => (v i : ℝ)) =
      ((L.qf v : ℤ) : ℝ) := by
    simp only [qf, bf, star_trivial, dotProduct, mulVec, Matrix.map_apply]
    push_cast
    rfl
  rw [e] at h
  exact_mod_cast h

theorem qf_nonneg (L : GramLattice ι) (v : ι → ℤ) : 0 ≤ L.qf v := by
  by_cases hv : v = 0
  · simp [hv, qf, bf]
  · exact (L.qf_pos hv).le

theorem qf_eq_zero_iff (L : GramLattice ι) {v : ι → ℤ} : L.qf v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact (L.qf_pos hv).ne' h
  · rintro rfl
    simp [qf, bf]

/-- The entries of `Xᵀ G Y` are the pairings of the columns. -/
theorem transpose_mul_mul_apply {κ μ : Type*} (L : GramLattice ι) (X : Matrix ι κ ℤ) (Y : Matrix ι μ ℤ)
    (i : κ) (j : μ) : (Xᵀ * L.gram * Y) i j = L.bf (fun a => X a i) (fun a => Y a j) := by
  simp only [bf, Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- A representation is a family of vectors with the prescribed pairings. -/
theorem represents_iff_vectors [Fintype κ] (L : GramLattice ι) (S : GramLattice κ) :
    L.Represents S ↔ ∃ x : κ → ι → ℤ, ∀ i j, L.bf (x i) (x j) = S.gram i j := by
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨fun i a => X a i, fun i j => ?_⟩
    rw [← hX, transpose_mul_mul_apply]
  · rintro ⟨x, hx⟩
    refine ⟨Matrix.of fun a i => x i a, ?_⟩
    ext i j
    rw [transpose_mul_mul_apply]
    exact hx i j

/-! ### Pullbacks -/

/-- `Bᵀ G B` is positive definite if `B` is injective on integer vectors. -/
theorem posDef_pullback_int [Fintype κ] [DecidableEq κ] (L : GramLattice ι) {B : Matrix ι κ ℤ}
    (hB : ∀ y : κ → ℤ, B *ᵥ y = 0 → y = 0) :
    ((Bᵀ * L.gram * B).map (Int.cast : ℤ → ℝ)).PosDef := by
  set M := Bᵀ * L.gram * B with hM
  -- no integer kernel
  have hker : ∀ y : κ → ℤ, M *ᵥ y = 0 → y = 0 := by
    intro y hy
    have h0 : L.qf (B *ᵥ y) = 0 := by
      have : y ⬝ᵥ (M *ᵥ y) = L.qf (B *ᵥ y) := by
        simp only [hM, qf, bf, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      rw [← this, hy, dotProduct_zero]
    exact hB y ((L.qf_eq_zero_iff).mp h0)
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    exact hy0 (hker y hy)
  have hpsd : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    rw [hM, map_intCast_transpose_mul_mul, ← conjTranspose_eq_transpose_of_trivial]
    exact L.posDef.posSemidef.conjTranspose_mul_mul_same _
  rw [posDef_iff_posSemidef_and_mulVec_injective]
  refine ⟨hpsd, ?_⟩
  exact mulVec_injective_iff_isUnit.mpr
    ((isUnit_iff_isUnit_det _).mpr (isUnit_det_map_intCast hdet))

/-- A matrix whose pulled-back Gram matrix is nonsingular is injective on integer vectors. -/
theorem injective_of_det [Fintype κ] [DecidableEq κ] (L : GramLattice ι) {B : Matrix ι κ ℤ}
    (h : (Bᵀ * L.gram * B).det ≠ 0) : ∀ y : κ → ℤ, B *ᵥ y = 0 → y = 0 := by
  intro y hy
  by_contra hy0
  apply h
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨y, hy0, ?_⟩
  rw [← mulVec_mulVec, hy, mulVec_zero]

/-- The lattice with Gram matrix `Bᵀ G_L B`, for `B` injective on integer vectors. -/
def ofPullback [Fintype κ] [DecidableEq κ] (L : GramLattice ι) (B : Matrix ι κ ℤ)
    (hB : ∀ y : κ → ℤ, B *ᵥ y = 0 → y = 0) : GramLattice κ where
  gram := Bᵀ * L.gram * B
  posDef := L.posDef_pullback_int hB

@[simp] theorem ofPullback_gram [Fintype κ] [DecidableEq κ] (L : GramLattice ι) (B : Matrix ι κ ℤ)
    (hB : ∀ y : κ → ℤ, B *ᵥ y = 0 → y = 0) : (L.ofPullback B hB).gram = Bᵀ * L.gram * B :=
  rfl

theorem represents_ofPullback [Fintype κ] [DecidableEq κ] (L : GramLattice ι) (B : Matrix ι κ ℤ)
    (hB : ∀ y : κ → ℤ, B *ᵥ y = 0 → y = 0) : L.Represents (L.ofPullback B hB) :=
  ⟨B, rfl⟩

/-- A matrix of nonzero determinant has no integer kernel. -/
theorem mulVec_eq_zero_of_det_ne_zero [DecidableEq ι] {W : Matrix ι ι ℤ} (hW : W.det ≠ 0)
    (y : ι → ℤ) (hy : W *ᵥ y = 0) : y = 0 := by
  have h := congrArg (fun v => W.adjugate *ᵥ v) hy
  simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, mulVec_zero] at h
  exact (smul_eq_zero.mp h).resolve_left hW

/-- **Change of basis.** The same lattice in the basis given by the columns of a unimodular `W`:
the Gram matrix `Wᵀ G W`. -/
def conj [DecidableEq ι] (S : GramLattice ι) (W : Matrix ι ι ℤ) (hW : IsUnit W.det) : GramLattice ι :=
  S.ofPullback W (mulVec_eq_zero_of_det_ne_zero hW.ne_zero)

@[simp] theorem conj_gram [DecidableEq ι] (S : GramLattice ι) (W : Matrix ι ι ℤ) (hW : IsUnit W.det) :
    (S.conj W hW).gram = Wᵀ * S.gram * W :=
  rfl

/-- A change of basis does not change the lattice: `S.conj W` represents `S` (and `S`
represents `S.conj W` via `⟨W, rfl⟩`). -/
theorem conj_represents [DecidableEq ι] (S : GramLattice ι) (W : Matrix ι ι ℤ) (hW : IsUnit W.det) :
    (S.conj W hW).Represents S := by
  refine ⟨W⁻¹, ?_⟩
  simp only [conj_gram]
  calc (W⁻¹)ᵀ * (Wᵀ * S.gram * W) * W⁻¹ = (W * W⁻¹)ᵀ * S.gram * (W * W⁻¹) := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = S.gram := by rw [mul_nonsing_inv _ hW]; simp

/-! ### Isometry -/

/-- `L` and `M` are isometric: some `X` with `Xᵀ G_L X = G_M` has an integral right inverse,
so its columns form a basis of `L`. -/
def Isometric [DecidableEq ι] [Fintype κ] (L : GramLattice ι) (M : GramLattice κ) : Prop :=
  ∃ X : Matrix ι κ ℤ, Xᵀ * L.gram * X = M.gram ∧ ∃ Y : Matrix κ ι ℤ, X * Y = 1

/-- A change of basis is an isometry. -/
theorem isometric_conj [DecidableEq ι] (L : GramLattice ι) (W : Matrix ι ι ℤ) (hW : IsUnit W.det) :
    L.Isometric (L.conj W hW) := by
  refine ⟨W, rfl, W.det • W.adjugate, ?_⟩
  rw [Matrix.mul_smul, mul_adjugate, smul_smul]
  rcases Int.isUnit_iff.mp hW with h | h <;> rw [h] <;> simp

theorem Isometric.represents [DecidableEq ι] [Fintype κ] {L : GramLattice ι} {M : GramLattice κ}
    (h : L.Isometric M) :
    L.Represents M := by
  obtain ⟨X, hX, -⟩ := h
  exact ⟨X, hX⟩

/-- A right inverse of an injective integer matrix is a two-sided inverse. -/
theorem mul_eq_one_comm_of_gram [DecidableEq ι] [Fintype κ] [DecidableEq κ] (L : GramLattice ι)
    (M : GramLattice κ) {X : Matrix ι κ ℤ} {Y : Matrix κ ι ℤ} (hX : Xᵀ * L.gram * X = M.gram)
    (hXY : X * Y = 1) : Y * X = 1 := by
  -- `X` is injective on integer vectors (its Gram matrix is positive definite)
  have hinj : ∀ y : κ → ℤ, X *ᵥ y = 0 → y = 0 := by
    intro y hy
    have : M.qf y = L.qf (X *ᵥ y) := by
      simp only [qf, bf, ← hX, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [hy] at this
    exact (M.qf_eq_zero_iff).mp (by rw [this]; simp [qf, bf])
  -- `X (Y X - 1) = 0`
  have h : X * (Y * X - 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hXY, Matrix.one_mul, Matrix.mul_one, sub_self]
  ext i j
  have hcol := hinj (fun a => ((Y * X - 1 : Matrix κ κ ℤ)) a j) (by
    funext a
    have := congrFun (congrFun h a) j
    simpa [Matrix.mul_apply, mulVec, dotProduct] using this)
  have := congrFun hcol i
  simpa [sub_eq_zero] using this

theorem Isometric.refl [DecidableEq ι] (L : GramLattice ι) : L.Isometric L :=
  ⟨1, by simp, 1, by simp⟩

theorem Isometric.symm [DecidableEq ι] [Fintype κ] [DecidableEq κ] {L : GramLattice ι} {M : GramLattice κ}
    (h : L.Isometric M) : M.Isometric L := by
  obtain ⟨X, hX, Y, hXY⟩ := h
  have hYX := mul_eq_one_comm_of_gram L M hX hXY
  refine ⟨Y, ?_, X, hYX⟩
  rw [← hX]
  calc Yᵀ * (Xᵀ * L.gram * X) * Y = (X * Y)ᵀ * L.gram * (X * Y) := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = L.gram := by rw [hXY]; simp

theorem Isometric.trans [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ]
    {L : GramLattice ι} {M : GramLattice κ} {N : GramLattice μ}
    (h₁ : L.Isometric M) (h₂ : M.Isometric N) : L.Isometric N := by
  obtain ⟨X, hX, Y, hXY⟩ := h₁
  obtain ⟨X', hX', Y', hXY'⟩ := h₂
  refine ⟨X * X', ?_, Y' * Y, ?_⟩
  · rw [← hX', ← hX]
    simp only [transpose_mul, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc X' Y', hXY', Matrix.one_mul, hXY]

theorem Isometric.represents_iff [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] {L : GramLattice ι}
    {M : GramLattice κ} (h : L.Isometric M) {S : GramLattice μ} :
    L.Represents S ↔ M.Represents S :=
  ⟨fun hS => h.symm.represents.trans hS, fun hS => h.represents.trans hS⟩

theorem Isometric.isUniversal_iff [DecidableEq ι] [Fintype κ] [DecidableEq κ] {L : GramLattice ι}
    {M : GramLattice κ} (h : L.Isometric M) {n : ℕ} : L.IsUniversal n ↔ M.IsUniversal n :=
  ⟨fun hL _ hm S => h.represents_iff.mp (hL hm S), fun hM _ hm S => h.represents_iff.mpr (hM hm S)⟩

/-- Reindexing gives an isometric lattice. -/
theorem isometric_reindex [DecidableEq ι] [Fintype κ] [DecidableEq κ] (L : GramLattice ι) (e : ι ≃ κ) :
    L.Isometric (L.reindex e) := by
  refine ⟨Matrix.of fun a i => if a = e.symm i then 1 else 0, ?_,
    Matrix.of fun i a => if a = e.symm i then 1 else 0, ?_⟩
  · ext i j
    simp [Matrix.mul_apply, reindex]
  · ext a b
    simp only [Matrix.mul_apply, of_apply]
    rw [Finset.sum_eq_single (e a)]
    · simp [Matrix.one_apply, eq_comm]
    · intro i _ hi
      have : a ≠ e.symm i := fun h => hi (by rw [h, Equiv.apply_symm_apply])
      simp [this]
    · simp

end GramLattice

end KimKimOh

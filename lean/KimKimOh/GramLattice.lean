import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# Positive-definite integral lattices as Gram matrices

A positive-definite integral lattice is a free `ℤ`-module of finite rank with a
positive-definite symmetric `ℤ`-valued bilinear form. We record such a lattice by its
Gram matrix in a basis indexed by a finite type `ι`: an integer matrix whose real form is
positive definite in the sense of `Matrix.PosDef` (which includes symmetry).

* `GramLattice ι` — the lattice;
* `GramLattice.Represents L S` — `S` embeds isometrically in `L`: some integer matrix `X`
  (whose columns are the images of the basis of `S`) has `Xᵀ G_L X = G_S`;
* `GramLattice.IsUniversal n L` — `L` represents every lattice of rank at most `n`;
* `GramLattice.orthSum` — the orthogonal sum `L ⊥ M`, indexed by `ι ⊕ κ`;
* `GramLattice.reindex` — the same lattice with its basis relabelled;
* `posDef_of_pullback` — if `Mᵀ A M` is a Gram matrix and `det M ≠ 0`, then `A` is positive
  definite (used for overlattices). Pullbacks `Bᵀ G B` are in `GramLattice/Isometry.lean`.

`posDef_of_ldl` proves positive definiteness of a concrete real matrix from an explicit
factorization `G = Uᵀ diag(d) U` with `d > 0` and `U` left-invertible. Mathlib has no
Sylvester criterion, and this factorization is easy to check entrywise.

The convention is an integral Gram matrix with real positive definiteness.
-/

namespace KimKimOh

open Matrix

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- A positive-definite integral lattice, presented by its Gram matrix `((eᵢ, eⱼ))` in a
basis indexed by `ι`. The real Gram matrix is positive definite, and in particular
symmetric. -/
structure GramLattice (ι : Type*) [Fintype ι] where
  /-- The Gram matrix, with integer entries. -/
  gram : Matrix ι ι ℤ
  /-- The Gram matrix is positive definite as a real matrix. -/
  posDef : (gram.map (Int.cast : ℤ → ℝ)).PosDef

/-- Positive definiteness of a real matrix from a factorization `G = Uᵀ diag(d) U` with
positive `d` and a left inverse `V` of `U`. -/
theorem posDef_of_ldl [DecidableEq ι] {G U V : Matrix ι ι ℝ} {d : ι → ℝ}
    (hd : ∀ i, 0 < d i) (hVU : V * U = 1) (hG : G = Uᵀ * diagonal d * U) : G.PosDef := by
  have hinj : Function.Injective U.mulVec := by
    intro x y hxy
    have h := congrArg V.mulVec hxy
    simpa [mulVec_mulVec, hVU] using h
  have h := (PosDef.diagonal hd).conjTranspose_mul_mul_same hinj
  rwa [conjTranspose_eq_transpose_of_trivial, ← hG] at h

namespace GramLattice

/-- A lattice is determined by its Gram matrix. -/
theorem ext {L M : GramLattice ι} (h : L.gram = M.gram) : L = M := by
  cases L; cases M; cases h; rfl

/-- The Gram matrix of a lattice is symmetric. -/
theorem gram_isSymm (L : GramLattice ι) : L.gram.IsSymm := by
  ext i j
  have h := congrFun (congrFun L.posDef.isHermitian i) j
  simp only [conjTranspose_apply, map_apply, star_trivial] at h
  simpa using (Int.cast_injective h)

theorem gram_comm (L : GramLattice ι) (i j : ι) : L.gram i j = L.gram j i :=
  congrFun (congrFun L.gram_isSymm j) i

/-- The Gram determinant of a lattice is positive. -/
theorem gram_det_pos [DecidableEq ι] (L : GramLattice ι) : 0 < L.gram.det := by
  have h := L.posDef.det_pos
  rw [show L.gram.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix L.gram from rfl,
    ← RingHom.map_det, eq_intCast] at h
  exact_mod_cast h

/-! ### Representations -/

/-- `L` represents `S`: there is an isometric embedding of `S` into `L`. It is given by an
integer matrix `X : Matrix ι κ ℤ` whose columns are the images of the basis vectors of `S`,
with `Xᵀ G_L X = G_S`. Such an `X` is automatically injective because `S` is positive
definite. -/
def Represents (L : GramLattice ι) (S : GramLattice κ) : Prop :=
  ∃ X : Matrix ι κ ℤ, Xᵀ * L.gram * X = S.gram

/-- `L` is `n`-universal: it represents every positive-definite integral lattice of rank at
most `n`. Every lattice of rank `m` has a basis indexed by `Fin m`; see
`IsUniversal.represents` for sources indexed by an arbitrary finite type. -/
def IsUniversal (n : ℕ) (L : GramLattice ι) : Prop :=
  ∀ ⦃m : ℕ⦄, m ≤ n → ∀ S : GramLattice (Fin m), L.Represents S

/-- Every lattice represents itself. -/
theorem Represents.refl (L : GramLattice ι) [DecidableEq ι] : L.Represents L :=
  ⟨1, by simp⟩

/-- Representations compose. -/
theorem Represents.trans {L : GramLattice ι} {M : GramLattice κ} {S : GramLattice μ}
    (hLM : L.Represents M) (hMS : M.Represents S) : L.Represents S := by
  obtain ⟨Y, hY⟩ := hLM
  obtain ⟨X, hX⟩ := hMS
  refine ⟨Y * X, ?_⟩
  rw [transpose_mul, ← hX, ← hY]
  simp only [Matrix.mul_assoc]

/-! ### Relabelling the basis -/

/-- The same lattice with its basis relabelled along `e : ι ≃ κ`. -/
def reindex (L : GramLattice ι) (e : ι ≃ κ) : GramLattice κ where
  gram := L.gram.submatrix e.symm e.symm
  posDef := by
    have h := L.posDef.submatrix (e := e.symm) e.symm.injective
    simpa [submatrix_map] using h

@[simp] theorem reindex_gram (L : GramLattice ι) (e : ι ≃ κ) :
    (L.reindex e).gram = L.gram.submatrix e.symm e.symm :=
  rfl

/-- Restricting the columns of `X` along `e` conjugates `Xᵀ G X` by `e`. -/
theorem conj_submatrix {ι κ μ : Type*} [Fintype ι] (X : Matrix ι κ ℤ) (G : Matrix ι ι ℤ)
    (e : μ → κ) :
    (X.submatrix id e)ᵀ * G * X.submatrix id e = (Xᵀ * G * X).submatrix e e := by
  ext i j
  simp [Matrix.mul_apply]

/-- A source can be relabelled. -/
theorem represents_reindex_iff (L : GramLattice μ) (S : GramLattice ι) (e : ι ≃ κ) :
    L.Represents (S.reindex e) ↔ L.Represents S := by
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨X.submatrix id e, ?_⟩
    rw [conj_submatrix, hX, reindex_gram, submatrix_submatrix]
    simp
  · rintro ⟨X, hX⟩
    refine ⟨X.submatrix id e.symm, ?_⟩
    rw [conj_submatrix, hX, reindex_gram]

/-- An `n`-universal lattice represents every lattice of rank at most `n`, whatever the
index type of its basis. -/
theorem IsUniversal.represents {n : ℕ} {L : GramLattice ι}
    (hL : L.IsUniversal n) (S : GramLattice κ) (hS : Fintype.card κ ≤ n) :
    L.Represents S := by
  have e := Fintype.equivFin κ
  exact (represents_reindex_iff L S e).mp (hL (by simpa using hS) _)

end GramLattice

/-! ### Sublattices and overlattices -/

omit [Fintype κ] in
/-- The real matrix of `Pᵀ G P` is computed from the real matrices of `P` and `G`. -/
theorem map_intCast_transpose_mul_mul (P : Matrix ι κ ℤ) (G : Matrix ι ι ℤ) :
    (Pᵀ * G * P).map (Int.cast : ℤ → ℝ) =
      (P.map (Int.cast : ℤ → ℝ))ᵀ * G.map (Int.cast : ℤ → ℝ) * P.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [map_apply, Matrix.mul_apply, transpose_apply]
  push_cast
  rfl

theorem isUnit_det_map_intCast [DecidableEq ι] {P : Matrix ι ι ℤ} (hP : P.det ≠ 0) :
    IsUnit (P.map (Int.cast : ℤ → ℝ)).det := by
  rw [isUnit_iff_ne_zero,
    show P.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix P from rfl, ← RingHom.map_det,
    eq_intCast]
  exact_mod_cast hP

namespace GramLattice

/-- **Overlattices.** If `Mᵀ A M` is the Gram matrix of `L` and `det M ≠ 0`, then `A` is
positive definite: over `ℝ` it is the pullback of `G_L` along `M⁻¹`. -/
theorem posDef_of_pullback [DecidableEq ι] (L : GramLattice ι) {A M : Matrix ι ι ℤ}
    (hM : M.det ≠ 0) (h : Mᵀ * A * M = L.gram) : (A.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hMR := isUnit_det_map_intCast hM
  have hL := L.posDef.conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.mpr
    ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hMR)))
  rw [← h, map_intCast_transpose_mul_mul, conjTranspose_eq_transpose_of_trivial] at hL
  convert hL using 1
  simp only [← Matrix.mul_assoc, ← transpose_mul, mul_nonsing_inv _ hMR, transpose_one,
    Matrix.one_mul]
  rw [Matrix.mul_assoc, mul_nonsing_inv _ hMR, Matrix.mul_one]

/-! ### Orthogonal sums -/

/-- The orthogonal sum `L ⊥ M`, with basis indexed by `ι ⊕ κ`. -/
def orthSum (L : GramLattice ι) (M : GramLattice κ) : GramLattice (ι ⊕ κ) where
  gram := fromBlocks L.gram 0 0 M.gram
  posDef := by
    rw [fromBlocks_map, Matrix.map_zero _ (Int.cast_zero), Matrix.map_zero _ (Int.cast_zero)]
    refine PosDef.of_dotProduct_mulVec_pos
      (L.posDef.isHermitian.fromBlocks (by simp) M.posDef.isHermitian) fun x hx => ?_
    set A := L.gram.map (Int.cast : ℤ → ℝ)
    set D := M.gram.map (Int.cast : ℤ → ℝ)
    have hxe : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
    have key : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
          star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
      conv_lhs => rw [hxe]
      rw [fromBlocks_mulVec, Function.star_sumElim, sumElim_dotProduct_sumElim]
      simp
    rw [key]
    by_cases hl : x ∘ Sum.inl = 0
    · have hr : x ∘ Sum.inr ≠ 0 := by
        intro hr
        apply hx
        rw [hxe, hl, hr]
        ext i
        cases i <;> rfl
      rw [hl]
      simpa using M.posDef.dotProduct_mulVec_pos hr
    · have h₁ := L.posDef.dotProduct_mulVec_pos hl
      have h₂ := M.posDef.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
      linarith

@[simp] theorem orthSum_gram (L : GramLattice ι) (M : GramLattice κ) :
    (L.orthSum M).gram = fromBlocks L.gram 0 0 M.gram :=
  rfl

/-- `L ⊥ M` represents `L`, via the first summand. -/
theorem represents_orthSum_left [DecidableEq ι] (L : GramLattice ι) (M : GramLattice κ) :
    (L.orthSum M).Represents L :=
  ⟨Matrix.of fun p i => Sum.elim (fun a => if a = i then 1 else 0) (fun _ => 0) p, by
    ext i j
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type, Function.swap]⟩

end GramLattice

end KimKimOh

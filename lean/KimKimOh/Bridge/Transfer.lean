import KimKimOh.Bridge.Padic
import KimKimOh.Hosts
import KimKimOh.Genus.K3K9Symbols
import QuadFormsKB.Literature.Watson1963.Perfect

/-!
# From `GramLattice` to Hanke's integral forms

A host `K : GramLattice ι` and an integer matrix `g` on `Fin m` with `g = K.gram` after relabelling
the basis by `e : Fin m ≃ ι`. Then:

* `repOver_of_locallyRepresents`: if `K` represents `S` modulo every `pᵏ`, then `ofMatrixZ g`
  represents `ofMatrixZ S.gram` over `ℤ_p` (`exists_padic_rep`);
* `represents_of_rep`: if `ofMatrixZ g` represents `ofMatrixZ S.gram` over `ℤ`, then `K`
  represents `S` (polarization);
* `posDef_ofMatrixZ`: the form of a `GramLattice` is positive definite.

`K3` and `K9` are related to `Genera.g3`, `Genera.g9` (with `A₂` first) by `relabelK3`, `relabelK9`.
-/

open Matrix QuadFormsKB QuadFormsKB.LocalDensity

namespace KimKimOh

variable {n v : ℕ}

/-- `ofMatrixZ M` evaluates to `xᵀ M x` over any commutative ring. -/
theorem evalIn_ofMatrixZ (R : Type*) [CommRing R] (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → R) :
    (ofMatrixZ M).evalIn R x = x ⬝ᵥ (M.map (Int.cast : ℤ → R) *ᵥ x) := by
  have hL : (ofMatrixZ M).evalIn R x = ∑ i, ∑ j, ((if i < j then (M i j : R) * x i * x j else 0)
      + (if i < j then (M j i : R) * x j * x i else 0)
      + (if i = j then (M i j : R) * x i * x j else 0)) := by
    simp only [QuadForm.evalIn, ofMatrixZ, Matrix.of_apply, algebraMap_int_eq, eq_intCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.le, h.ne]; ring
    · simp
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
  have hR : x ⬝ᵥ (M.map (Int.cast : ℤ → R) *ᵥ x) = ∑ i, ∑ j,
      ((if i < j then (M i j : R) * x i * x j else 0)
      + (if j < i then (M i j : R) * x i * x j else 0)
      + (if i = j then (M i j : R) * x i * x j else 0)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le, h.ne]; ring
    · simp; ring
    · simp [h, not_lt.mpr h.le, h.ne']; ring
  rw [hL, hR]
  simp only [Finset.sum_add_distrib]
  congr 2
  rw [Finset.sum_comm]

/-- `(H y)ᵀ K (H y) = yᵀ (Hᵀ K H) y`. -/
theorem quad_mulVec {R : Type*} [CommRing R] (K : Matrix (Fin n) (Fin n) R) (H : Matrix (Fin n) (Fin v) R)
    (y : Fin v → R) : (H *ᵥ y) ⬝ᵥ (K *ᵥ (H *ᵥ y)) = y ⬝ᵥ ((Hᵀ * K * H) *ᵥ y) := by
  have e : H *ᵥ y = y ᵥ* Hᵀ := (Matrix.vecMul_transpose H y).symm
  rw [Matrix.dotProduct_mulVec (H *ᵥ y) K (H *ᵥ y), e, Matrix.vecMul_vecMul, ← e,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- Polarization: two symmetric integer matrices with the same quadratic form are equal. -/
theorem eq_of_quad_eq {A B : Matrix (Fin v) (Fin v) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : ∀ y : Fin v → ℤ, y ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (B *ᵥ y)) : A = B := by
  have hd : ∀ i, A i i = B i i := fun i => by
    simpa [Matrix.mulVec_single, dotProduct_single] using h (Pi.single i 1)
  ext i j
  by_cases hij : i = j
  · subst hij; exact hd i
  have hAji : A j i = A i j := congrFun (congrFun hA i) j
  have hBji : B j i = B i j := congrFun (congrFun hB i) j
  have h2 := h (Pi.single i 1 + Pi.single j 1)
  simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single,
    single_dotProduct] at h2
  linarith [hd i, hd j]

/-- An integral matrix representation gives a `Rep`. -/
theorem rep_of_matrix {n v : ℕ} {g : Matrix (Fin n) (Fin n) ℤ} {S : Matrix (Fin v) (Fin v) ℤ}
    (H : Matrix (Fin n) (Fin v) ℤ) (hH : Hᵀ * g * H = S) : Watson1963.Rep (ofMatrixZ g) (ofMatrixZ S) :=
  ⟨H, fun y => by rw [eval_ofMatrixZ, eval_ofMatrixZ, quad_mulVec, hH]⟩

/-- A `Rep` gives an integral matrix representation (polarization). -/
theorem matrix_of_rep {n v : ℕ} {g : Matrix (Fin n) (Fin n) ℤ} (hgs : gᵀ = g) (S : GramLattice (Fin v))
    (h : Watson1963.Rep (ofMatrixZ g) (ofMatrixZ S.gram)) : ∃ H : Matrix (Fin n) (Fin v) ℤ, Hᵀ * g * H = S.gram := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H, eq_of_quad_eq ?_ S.gram_isSymm.eq fun y => ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hgs, Matrix.mul_assoc]
  · have := hH y
    rw [eval_ofMatrixZ, eval_ofMatrixZ, quad_mulVec] at this
    exact this

namespace GramLattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The form `xᵀ G x` of a lattice is positive on nonzero integer vectors. -/
theorem posDef_ofMatrixZ (S : GramLattice (Fin v)) : IntQF.PosDef (ofMatrixZ S.gram) := by
  intro x hx
  rw [eval_ofMatrixZ]
  have hx' : (fun i => (x i : ℝ)) ≠ 0 := fun h => hx (funext fun i => by simpa using congrFun h i)
  have h := S.posDef.dotProduct_mulVec_pos hx'
  have e : star (fun i => (x i : ℝ)) ⬝ᵥ (S.gram.map (Int.cast : ℤ → ℝ) *ᵥ fun i => (x i : ℝ)) =
      ((x ⬝ᵥ (S.gram *ᵥ x) : ℤ) : ℝ) := by
    simp [dotProduct, mulVec, Matrix.map_apply]
  rw [e] at h
  exact_mod_cast h

omit [DecidableEq ι] in
/-- **Local representations transfer** along a relabelling `g = K.gram ∘ (e × e)`. -/
theorem repOver_of_locallyRepresents (K : GramLattice ι) {m : ℕ} (e : Fin m ≃ ι)
    (g : Matrix (Fin m) (Fin m) ℤ) (hg : g = K.gram.submatrix e e) (S : GramLattice (Fin v))
    (p : ℕ) [Fact p.Prime] (h : LocallyRepresents K.gram S.gram p) :
    Watson1963.RepOver ℤ_[p] (ofMatrixZ g) (ofMatrixZ S.gram) := by
  obtain ⟨H, hH⟩ := exists_padic_rep p K.gram S.gram h
  refine ⟨H.submatrix e id, fun y => ?_⟩
  have hc : (H.submatrix e id)ᵀ * g.map (Int.cast : ℤ → ℤ_[p]) * H.submatrix e id =
      S.gram.map (Int.cast : ℤ → ℤ_[p]) := by
    rw [hg, ← hH, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    rfl
  rw [evalIn_ofMatrixZ, evalIn_ofMatrixZ, quad_mulVec, hc]

omit [DecidableEq ι] in
/-- **Global representations transfer back** along the relabelling. -/
theorem represents_of_rep (K : GramLattice ι) {m : ℕ} (e : Fin m ≃ ι)
    (g : Matrix (Fin m) (Fin m) ℤ) (hg : g = K.gram.submatrix e e) (S : GramLattice (Fin v))
    (h : Watson1963.Rep (ofMatrixZ g) (ofMatrixZ S.gram)) : K.Represents S := by
  have hgs : gᵀ = g := by rw [hg, Matrix.transpose_submatrix, K.gram_isSymm.eq]
  obtain ⟨H, hq⟩ := matrix_of_rep hgs S h
  refine ⟨H.submatrix e.symm id, ?_⟩
  have hK : K.gram = g.submatrix e.symm e.symm := by
    rw [hg]; ext i j; simp
  rw [hK, ← hq, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

end GramLattice

/-! ### `K₃` and `K₉` in the coordinates of `Genera` -/

/-- `Fin 5 ≃ Fin 3 ⊕ Fin 2`: the `A₂` coordinates of `g3` first. -/
def relabelK3Fun : Fin 5 → Fin 3 ⊕ Fin 2 := ![.inr 0, .inr 1, .inl 0, .inl 1, .inl 2]

/-- `Fin 5 ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin 1`: the `A₂` and `⟨3⟩` coordinates of `g9` first. -/
def relabelK9Fun : Fin 5 → (Fin 2 ⊕ Fin 2) ⊕ Fin 1 := ![.inl (.inr 0), .inl (.inr 1), .inr 0, .inl (.inl 0), .inl (.inl 1)]

/-- The relabelling of `K₃`. -/
noncomputable def relabelK3 : Fin 5 ≃ Fin 3 ⊕ Fin 2 := Equiv.ofBijective relabelK3Fun (by decide)

/-- The relabelling of `K₉`. -/
noncomputable def relabelK9 : Fin 5 ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin 1 := Equiv.ofBijective relabelK9Fun (by decide)

theorem g3_eq_K3 : Genera.g3 = K3.gram.submatrix relabelK3 relabelK3 := by
  rw [Genera.g3_eq]; decide

theorem g9_eq_K9 : Genera.g9 = K9.gram.submatrix relabelK9 relabelK9 := by
  rw [Genera.g9_eq]; decide

end KimKimOh

import KimKimOh.Genus.Kko112Genus
import KimKimOh.Genus.Kko112Data

/-!
# From `K₆` to `K₂₂`: Lemma 1 of Kim–Kim–Oh, §4

Let `X` (5 x 2) represent a binary `S = Xᵀ K₆ X` by `K₆ = ⟨6⟩ ⊥ I₄` (`Genera.k6`). Kim–Kim–Oh's
Lemma 1 shows that `K₂₂` represents `S` unless `S` is even unimodular over `ℤ₂` and
`d S ≡ 1 (mod 3)`. We prove it with transfer matrices (`rep_of_k6`):

* `trMat c e = c B + λ w̃ᵀ` (`e = (w, λ, B)` from `tr2`, `tr3`, `c = 2, 3`) satisfies
  `Aᵀ K₂₂ A = c² K₆` (`tr2_spec`, `tr3_spec`). If the top four rows `x, y` of `X` (the `I₄`
  coordinates) are orthogonal to `w` modulo `c`, then `c ∣ A X` and `Y = A X / c` represents `S`
  by `K₂₂` (`rep_of_transfer`).
* Modulo 2 and modulo 3, every pair `x, y` is orthogonal to one of the six (sixteen) `w`, unless
  `x·x ≡ y·y ≡ 0`, `x·y ≡ 1 (mod 2)` (`orth_or_exception_two`), resp.
  `(x·x)(y·y) - (x·y)² ≡ 1 (mod 3)` (`orth_or_exception_three`), checked by the kernel. Since
  `S ≡ (x·x, x·y, y·y)` modulo 2 and modulo 3, the exceptions are exactly the binaries with
  `S₀₀, S₁₁` even, `S₀₁` odd and `det S ≡ 1 (mod 3)`.
-/

open Matrix

namespace KimKimOh.Kko112

open Genera

/-- The transfer matrix `c B + λ w̃ᵀ` of `e = (w, λ, B)`, `w̃ = (0, w)`. -/
def trMat (c : ℤ) (e : List ℤ × List ℤ × List ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun k j => c * e.2.2.getD (5 * k.val + j.val) 0 +
    e.2.1.getD k.val 0 * (if j.val = 0 then 0 else e.1.getD (j.val - 1) 0)

theorem tr2_spec : ∀ i : Fin 6, (trMat 2 (tr2.getD i.val ([], [], [])))ᵀ * g22 * trMat 2 (tr2.getD i.val ([], [], [])) =
    (2 ^ 2 : ℤ) • k6 := by
  rw [g22_eq, k6_eq]; decide +kernel

theorem tr3_spec : ∀ i : Fin 16, (trMat 3 (tr3.getD i.val ([], [], [])))ᵀ * g22 * trMat 3 (tr3.getD i.val ([], [], [])) =
    (3 ^ 2 : ℤ) • k6 := by
  rw [g22_eq, k6_eq]; decide +kernel

/-- The dot product on `Fin 4`. -/
def dot4 {R : Type*} [CommRing R] (u v : Fin 4 → R) : R := u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

/-- The vector `w` of a transfer, modulo `c`. -/
def wvec (c : ℕ) (e : List ℤ × List ℤ × List ℤ) : Fin 4 → ZMod c := fun j => (e.1.getD j.val 0 : ZMod c)

theorem orth_or_exception_two : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : ZMod 2,
    (∃ i : Fin 6, dot4 (wvec 2 (tr2.getD i.val ([], [], []))) ![a0, a1, a2, a3] = 0 ∧
      dot4 (wvec 2 (tr2.getD i.val ([], [], []))) ![b0, b1, b2, b3] = 0) ∨
    (dot4 ![a0, a1, a2, a3] ![a0, a1, a2, a3] = 0 ∧ dot4 ![b0, b1, b2, b3] ![b0, b1, b2, b3] = 0 ∧
      dot4 ![a0, a1, a2, a3] ![b0, b1, b2, b3] = 1) := by
  decide +kernel

theorem orth_or_exception_three : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : ZMod 3,
    (∃ i : Fin 16, dot4 (wvec 3 (tr3.getD i.val ([], [], []))) ![a0, a1, a2, a3] = 0 ∧
      dot4 (wvec 3 (tr3.getD i.val ([], [], []))) ![b0, b1, b2, b3] = 0) ∨
    dot4 ![a0, a1, a2, a3] ![a0, a1, a2, a3] * dot4 ![b0, b1, b2, b3] ![b0, b1, b2, b3] -
      dot4 ![a0, a1, a2, a3] ![b0, b1, b2, b3] ^ 2 = 1 := by
  decide +kernel

/-- The top four rows of a column of `X`, modulo `c`. -/
def topVec (c : ℕ) (X : Matrix (Fin 5) (Fin 2) ℤ) (l : Fin 2) : Fin 4 → ZMod c :=
  ![(X 1 l : ZMod c), (X 2 l : ZMod c), (X 3 l : ZMod c), (X 4 l : ZMod c)]

/-- **The transfer.** If `Aᵀ K₂₂ A = c² K₆` and `c ∣ A X`, then `A X / c` represents `Xᵀ K₆ X`. -/
theorem rep_of_transfer {A : Matrix (Fin 5) (Fin 5) ℤ} {c : ℤ} (hc : c ≠ 0) (hA : Aᵀ * g22 * A = (c ^ 2) • k6)
    (X : Matrix (Fin 5) (Fin 2) ℤ) (hdiv : ∀ k l, c ∣ (A * X) k l) :
    ∃ Y : Matrix (Fin 5) (Fin 2) ℤ, Yᵀ * g22 * Y = Xᵀ * k6 * X := by
  refine ⟨Matrix.of fun k l => (A * X) k l / c, ?_⟩
  have hY : c • (Matrix.of fun k l => (A * X) k l / c) = A * X := by
    ext k l; simp [Int.mul_ediv_cancel' (hdiv k l)]
  have key : (c ^ 2) • ((Matrix.of fun k l => (A * X) k l / c)ᵀ * g22 * Matrix.of fun k l => (A * X) k l / c) =
      (c ^ 2) • (Xᵀ * k6 * X) := by
    have e1 : (c ^ 2) • ((Matrix.of fun k l => (A * X) k l / c)ᵀ * g22 * Matrix.of fun k l => (A * X) k l / c) =
        (c • (Matrix.of fun k l => (A * X) k l / c))ᵀ * g22 * (c • Matrix.of fun k l => (A * X) k l / c) := by
      rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
    have e2 : (A * X)ᵀ * g22 * (A * X) = Xᵀ * (Aᵀ * g22 * A) * X := by
      rw [transpose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, hY, e2, hA, Matrix.mul_smul, Matrix.smul_mul]
  ext k l
  have := congrFun (congrFun key k) l
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ (pow_ne_zero 2 hc) this

theorem dot4_wvec_topVec (c : ℕ) (e : List ℤ × List ℤ × List ℤ) (X : Matrix (Fin 5) (Fin 2) ℤ) (l : Fin 2) :
    dot4 (wvec c e) (topVec c X l) = ((e.1.getD 0 0 * X 1 l + e.1.getD 1 0 * X 2 l + e.1.getD 2 0 * X 3 l +
      e.1.getD 3 0 * X 4 l : ℤ) : ZMod c) := by
  push_cast; rfl

/-- `c ∣ trMat c e * X` when the top rows of `X` are orthogonal to `w` modulo `c`. -/
theorem trMat_dvd (c : ℕ) (e : List ℤ × List ℤ × List ℤ) (X : Matrix (Fin 5) (Fin 2) ℤ)
    (h : ∀ l, dot4 (wvec c e) (topVec c X l) = 0) : ∀ k l, (c : ℤ) ∣ (trMat c e * X) k l := by
  intro k l
  have hsum : (trMat c e * X) k l = c * ∑ j, e.2.2.getD (5 * k.val + j.val) 0 * X j l +
      e.2.1.getD k.val 0 * (e.1.getD 0 0 * X 1 l + e.1.getD 1 0 * X 2 l + e.1.getD 2 0 * X 3 l +
        e.1.getD 3 0 * X 4 l) := by
    simp only [trMat, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_five]
    simp
    ring
  rw [hsum]
  refine dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right ?_ _)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have := h l
  rw [dot4_wvec_topVec] at this
  exact this

/-- `S = Xᵀ K₆ X` in coordinates. -/
theorem k6_entry (X : Matrix (Fin 5) (Fin 2) ℤ) (l m : Fin 2) :
    (Xᵀ * k6 * X) l m = 6 * X 0 l * X 0 m + X 1 l * X 1 m + X 2 l * X 2 m + X 3 l * X 3 m + X 4 l * X 4 m := by
  have hk : ∀ i j : Fin 5, k6 i j = if i = j then (if i = 0 then (6 : ℤ) else 1) else 0 := by
    intro i j; rw [k6_eq]; fin_cases i <;> fin_cases j <;> rfl
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five, hk]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

theorem k6_entry_cast (c : ℕ) (hc : (6 : ZMod c) = 0) (X : Matrix (Fin 5) (Fin 2) ℤ) (l m : Fin 2) :
    (((Xᵀ * k6 * X) l m : ℤ) : ZMod c) = dot4 (topVec c X l) (topVec c X m) := by
  rw [k6_entry]
  push_cast
  rw [hc]
  simp [dot4, topVec]

/-- **Kim–Kim–Oh, §4, Lemma 1.** A binary represented by `K₆` is represented by `K₂₂`, unless it is
even with odd off-diagonal entry and determinant `≡ 1 (mod 3)`. -/
theorem rep_of_k6 (X : Matrix (Fin 5) (Fin 2) ℤ) :
    (∃ Y : Matrix (Fin 5) (Fin 2) ℤ, Yᵀ * g22 * Y = Xᵀ * k6 * X) ∨
      ((((Xᵀ * k6 * X) 0 0 : ℤ) : ZMod 2) = 0 ∧ (((Xᵀ * k6 * X) 1 1 : ℤ) : ZMod 2) = 0 ∧
        (((Xᵀ * k6 * X) 0 1 : ℤ) : ZMod 2) = 1 ∧ (((Xᵀ * k6 * X).det : ℤ) : ZMod 3) = 1) := by
  have h2 := orth_or_exception_two (X 1 0) (X 2 0) (X 3 0) (X 4 0) (X 1 1) (X 2 1) (X 3 1) (X 4 1)
  have h3 := orth_or_exception_three (X 1 0) (X 2 0) (X 3 0) (X 4 0) (X 1 1) (X 2 1) (X 3 1) (X 4 1)
  have hv : ∀ c : ℕ, ∀ l : Fin 2, topVec c X l = ![(X 1 l : ZMod c), (X 2 l : ZMod c), (X 3 l : ZMod c),
      (X 4 l : ZMod c)] := fun _ _ => rfl
  rcases h2 with ⟨i, hi0, hi1⟩ | ⟨hxx, hyy, hxy⟩
  · left
    refine rep_of_transfer (by norm_num) (tr2_spec i) X (trMat_dvd 2 _ X fun l => ?_)
    fin_cases l
    · exact hi0
    · exact hi1
  rcases h3 with ⟨i, hi0, hi1⟩ | hdet
  · left
    refine rep_of_transfer (by norm_num) (tr3_spec i) X (trMat_dvd 3 _ X fun l => ?_)
    fin_cases l
    · exact hi0
    · exact hi1
  right
  have c2 : (6 : ZMod 2) = 0 := by decide
  have c3 : (6 : ZMod 3) = 0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [k6_entry_cast 2 c2]; exact hxx
  · rw [k6_entry_cast 2 c2]; exact hyy
  · rw [k6_entry_cast 2 c2]; exact hxy
  · rw [det_fin_two]
    push_cast
    rw [k6_entry_cast 3 c3, k6_entry_cast 3 c3, k6_entry_cast 3 c3, k6_entry_cast 3 c3]
    have hs : dot4 (topVec 3 X 1) (topVec 3 X 0) = dot4 (topVec 3 X 0) (topVec 3 X 1) := by
      simp only [dot4]; ring
    rw [hs, ← sq]
    exact hdet

end KimKimOh.Kko112

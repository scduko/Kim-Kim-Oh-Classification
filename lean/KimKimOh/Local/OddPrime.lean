import KimKimOh.Local.Hensel
import KimKimOh.Hosts
import KimKimOh.Maximal
import KimKimOh.Ternary
import KimKimOh.SmallPrimes
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Seeds over finite fields (`lem:functional`)

This file supplies the finite-field input of Hensel's lemma (`KimKimOh.Local.Hensel`) for
the hosts at odd primes where they are unimodular, following the proof of `lem:functional`: the
host splits as two hyperbolic planes and a line, and a ternary of rank at least 2, or with
a diagonal entry in the determinant square class, embeds in that split form.

* `Isometric T T'` says that `T' = Pᵀ T P` for an invertible `P`. The elementary moves
  `isometric_swap*` and `isometric_shear*` diagonalize every ternary of rank at least 2
  (`exists_diag`) and split off a nonzero diagonal entry (`isometric_split`).
* `splitForm δ = H ⊥ H ⊥ ⟨δ⟩`, with `H` the hyperbolic plane. Over a finite field of odd
  characteristic `hostForm α p q r = ⟨1, 1, α⟩ ⊥ [[p, q], [q, r]]` contains
  `splitForm (α (pr - q²))` (`exists_splitForm`): an isotropic vector of `⟨1, 1, α⟩` and one
  of its complement `⟨-α⟩ ⊥ [[p, q], [q, r]]` span the two planes.
* `seed_splitForm_diag`, `seed_splitForm_line`: seeds in `splitForm δ` for a diagonal ternary
  with two nonzero entries, and for `⟨δ v²⟩ ⊥ B` with `B` any binary.
* `seed_hostForm_of_rank`, `seed_hostForm_of_square`: the two criteria of `lem:functional`
  over the field. `rank_of_hostForm`, `square_of_hostForm`: their lifts to `ℤ_p`, for `p ≥ 5`
  and a host containing `hostForm α s q r` with invariants among `1, 2, 3, 4, 6, 9`.
-/

namespace KimKimOh.Local.OddPrime

open Matrix

/-! ### Ternary matrices of rank 2 -/

/-- The six 2×2 minors of `ternMat a b c d e f` (in the order of `Tern.minors`) do not all
vanish: the matrix has rank at least 2. -/
def RankTwo {R : Type*} [CommRing R] (a b c d e f : R) : Prop :=
  ¬ (a * c - b * b = 0 ∧ a * f - d * d = 0 ∧ c * f - e * e = 0 ∧ a * e - b * d = 0 ∧
    b * e - c * d = 0 ∧ b * f - d * e = 0)

/-! ### Isometry of ternary matrices -/

section Field

variable {F : Type*} [Field F]

/-- `T'` is isometric to `T`: `T' = Pᵀ T P` for some `P` with a right inverse. -/
def Isometric (T T' : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∃ P Q : Matrix (Fin 3) (Fin 3) F, P * Q = 1 ∧ Pᵀ * T * P = T'

theorem Isometric.trans {T T' T'' : Matrix (Fin 3) (Fin 3) F} (h₁ : Isometric T T')
    (h₂ : Isometric T' T'') : Isometric T T'' := by
  obtain ⟨P₁, Q₁, h₁, e₁⟩ := h₁
  obtain ⟨P₂, Q₂, h₂, e₂⟩ := h₂
  refine ⟨P₁ * P₂, Q₂ * Q₁, ?_, ?_⟩
  · calc P₁ * P₂ * (Q₂ * Q₁) = P₁ * (P₂ * Q₂) * Q₁ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h₂, Matrix.mul_one, h₁]
  · rw [← e₂, ← e₁, transpose_mul]
    simp only [Matrix.mul_assoc]

theorem Isometric.of_eq {T T' T'' : Matrix (Fin 3) (Fin 3) F} (h : Isometric T T')
    (e : T' = T'') : Isometric T T'' :=
  e ▸ h

/-- A seed for an isometric matrix is a seed. -/
theorem Seed.of_isometric {ι : Type*} [Fintype ι] {K : Matrix ι ι F}
    {T T' : Matrix (Fin 3) (Fin 3) F} (h : Isometric T T') (hs : Seed K T') : Seed K T := by
  obtain ⟨P, Q, hPQ, e⟩ := h
  exact Seed.of_conj P Q hPQ (e ▸ hs)

/-- Proves an identity of explicit 3×3 matrices entrywise. -/
local macro "mat3" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [ternMat, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring))

theorem isometric_swap01 (a b c d e f : F) :
    Isometric (ternMat a b c d e f)
      (ternMat c b a e d f) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by mat3, by mat3⟩

theorem isometric_swap02 (a b c d e f : F) :
    Isometric (ternMat a b c d e f)
      (ternMat f e c d b a) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by mat3, by mat3⟩

theorem isometric_swap12 (a b c d e f : F) :
    Isometric (ternMat a b c d e f)
      (ternMat a d f b e c) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by mat3, by mat3⟩

theorem isometric_shear01 (a b c d e f l : F) :
    Isometric (ternMat a b c d e f)
      (ternMat a (b + l * a) (c + 2 * l * b + l ^ 2 * a) d (e + l * d) f) :=
  ⟨!![1, l, 0; 0, 1, 0; 0, 0, 1], !![1, -l, 0; 0, 1, 0; 0, 0, 1], by mat3, by mat3⟩

theorem isometric_shear02 (a b c d e f l : F) :
    Isometric (ternMat a b c d e f)
      (ternMat a b c (d + l * a) (e + l * b) (f + 2 * l * d + l ^ 2 * a)) :=
  ⟨!![1, 0, l; 0, 1, 0; 0, 0, 1], !![1, 0, -l; 0, 1, 0; 0, 0, 1], by mat3, by mat3⟩

theorem isometric_shear12 (a b c d e f l : F) :
    Isometric (ternMat a b c d e f)
      (ternMat a b c (d + l * b) (e + l * c) (f + 2 * l * e + l ^ 2 * c)) :=
  ⟨!![1, 0, 0; 0, 1, l; 0, 0, 1], !![1, 0, 0; 0, 1, -l; 0, 0, 1], by mat3, by mat3⟩

theorem isometric_shear21 (a b c d e f l : F) :
    Isometric (ternMat a b c d e f)
      (ternMat a (b + l * d) (c + 2 * l * e + l ^ 2 * f) d (e + l * f) f) :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, l, 1], !![1, 0, 0; 0, 1, 0; 0, -l, 1], by mat3, by mat3⟩

theorem isometric_shear10 (a b c d e f l : F) :
    Isometric (ternMat a b c d e f)
      (ternMat (a + 2 * l * b + l ^ 2 * c) (b + l * c) c (d + l * e) e f) :=
  ⟨!![1, 0, 0; l, 1, 0; 0, 0, 1], !![1, 0, 0; -l, 1, 0; 0, 0, 1], by mat3, by mat3⟩

theorem isometric_shear20 (a b c d e f l : F) :
    Isometric (ternMat a b c d e f)
      (ternMat (a + 2 * l * d + l ^ 2 * f) (b + l * e) c (d + l * f) e f) :=
  ⟨!![1, 0, 0; 0, 1, 0; l, 0, 1], !![1, 0, 0; 0, 1, 0; -l, 0, 1], by mat3, by mat3⟩

/-- Completing the square on a nonzero leading entry. -/
theorem isometric_split {a : F} (ha : a ≠ 0) (b c d e f : F) :
    Isometric (ternMat a b c d e f)
      (ternMat a 0 (c - b * b / a) 0 (e - b * d / a) (f - d * d / a)) := by
  refine ((isometric_shear01 a b c d e f (-b / a)).trans
    (isometric_shear02 _ _ _ _ _ _ (-d / a))).of_eq ?_
  congr 1 <;> field_simp <;> ring

/-- A binary block with a nonzero entry is diagonalizable with a nonzero first entry. -/
theorem isometric_diag_binary (h2 : (2 : F) ≠ 0) (a : F) {c e f : F}
    (h : ¬ (c = 0 ∧ e = 0 ∧ f = 0)) :
    ∃ t₂ t₃ : F, t₂ ≠ 0 ∧ Isometric (ternMat a 0 c 0 e f) (ternMat a 0 t₂ 0 0 t₃) := by
  have key : ∀ {c e f : F}, c ≠ 0 →
      Isometric (ternMat a 0 c 0 e f) (ternMat a 0 c 0 0 (f - e * e / c)) :=
    fun {c e f} hc => (isometric_shear12 a 0 c 0 e f (-e / c)).of_eq (by
      congr 1 <;> field_simp <;> ring)
  by_cases hc : c = 0
  · by_cases hf : f = 0
    · have he : e ≠ 0 := fun he => h ⟨hc, he, hf⟩
      have h2e : 2 * e ≠ 0 := mul_ne_zero h2 he
      refine ⟨2 * e, _, h2e, ((isometric_shear21 a 0 c 0 e f 1).of_eq ?_).trans
        (key (e := e) (f := 0) h2e)⟩
      subst hc hf
      congr 1 <;> ring
    · exact ⟨f, _, hf, (isometric_swap12 a 0 c 0 e f).trans (key hf)⟩
  · exact ⟨c, _, hc, key hc⟩

/-- Rank 2 is preserved by exchanging the first two coordinates. -/
theorem RankTwo.swap01 {a b c d e f : F} (h : RankTwo a b c d e f) : RankTwo c b a e d f := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  exact h ⟨by linear_combination h1, by linear_combination h3, by linear_combination h2,
    by linear_combination -h5, by linear_combination -h4, by linear_combination h6⟩

/-- Rank 2 is preserved by exchanging the first and the last coordinate. -/
theorem RankTwo.swap02 {a b c d e f : F} (h : RankTwo a b c d e f) : RankTwo f e c d b a := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  exact h ⟨by linear_combination h3, by linear_combination h2, by linear_combination h1,
    by linear_combination h6, by linear_combination h5, by linear_combination h4⟩

/-- Diagonalization with a nonzero leading entry: complete the square, then diagonalize the
remaining binary, which is nonzero because the ternary has rank 2. -/
theorem isometric_diag_pivot (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) {b c d e f : F}
    (h : RankTwo a b c d e f) :
    ∃ t₁ t₂ t₃ : F, t₁ ≠ 0 ∧ t₂ ≠ 0 ∧
      Isometric (ternMat a b c d e f) (ternMat t₁ 0 t₂ 0 0 t₃) := by
  have h' : ¬ (c - b * b / a = 0 ∧ e - b * d / a = 0 ∧ f - d * d / a = 0) := by
    rintro ⟨h₁, h₂, h₃⟩
    field_simp at h₁ h₂ h₃
    apply h
    refine ⟨by linear_combination h₁, by linear_combination h₃, ?_, by linear_combination h₂,
      ?_, ?_⟩
    · apply mul_left_cancel₀ (mul_ne_zero ha ha)
      linear_combination (a * f) * h₁ + (b * b) * h₃ - (a * e + b * d) * h₂
    · apply mul_left_cancel₀ ha
      linear_combination b * h₂ - d * h₁
    · apply mul_left_cancel₀ ha
      linear_combination b * h₃ - d * h₂
  obtain ⟨t₂, t₃, ht₂, hc⟩ := isometric_diag_binary h2 a h'
  exact ⟨a, t₂, t₃, ha, ht₂, (isometric_split ha b c d e f).trans hc⟩

/-- **Diagonalization.** A ternary of rank at least 2 over a field of characteristic
different from 2 is isometric to `diag(t₁, t₂, t₃)` with `t₁, t₂ ≠ 0`: move a nonzero
diagonal entry to the front, or create one by a shear if the diagonal vanishes, and pivot. -/
theorem exists_diag (h2 : (2 : F) ≠ 0) {a b c d e f : F} (h : RankTwo a b c d e f) :
    ∃ t₁ t₂ t₃ : F, t₁ ≠ 0 ∧ t₂ ≠ 0 ∧
      Isometric (ternMat a b c d e f) (ternMat t₁ 0 t₂ 0 0 t₃) := by
  by_cases ha : a ≠ 0
  · exact isometric_diag_pivot h2 ha h
  by_cases hc : c ≠ 0
  · obtain ⟨t₁, t₂, t₃, h₁, h₂, hT⟩ := isometric_diag_pivot h2 hc h.swap01
    exact ⟨t₁, t₂, t₃, h₁, h₂, (isometric_swap01 a b c d e f).trans hT⟩
  by_cases hf : f ≠ 0
  · obtain ⟨t₁, t₂, t₃, h₁, h₂, hT⟩ := isometric_diag_pivot h2 hf h.swap02
    exact ⟨t₁, t₂, t₃, h₁, h₂, (isometric_swap02 a b c d e f).trans hT⟩
  -- the diagonal vanishes: a shear makes the leading entry `2b`, `2d` or `2e`
  push Not at ha hc hf
  subst ha hc hf
  by_cases hb : b ≠ 0
  · obtain ⟨t₁, t₂, t₃, h₁, h₂, hT⟩ := isometric_diag_pivot h2 (mul_ne_zero h2 hb)
      (b := b) (c := 0) (d := d + e) (e := e) (f := 0)
      (by rintro ⟨h3, -⟩; exact hb (by simpa using h3))
    refine ⟨t₁, t₂, t₃, h₁, h₂, ((isometric_shear10 0 b 0 d e 0 1).of_eq ?_).trans hT⟩
    congr 1 <;> ring
  push Not at hb
  subst hb
  by_cases hd : d ≠ 0
  · obtain ⟨t₁, t₂, t₃, h₁, h₂, hT⟩ := isometric_diag_pivot h2 (mul_ne_zero h2 hd)
      (b := e) (c := 0) (d := d) (e := e) (f := 0)
      (by rintro ⟨-, h3, -⟩; exact hd (by simpa using h3))
    refine ⟨t₁, t₂, t₃, h₁, h₂, ((isometric_shear20 0 0 0 d e 0 1).of_eq ?_).trans hT⟩
    congr 1 <;> ring
  push Not at hd
  subst hd
  have he : e ≠ 0 := by rintro rfl; exact h (by simp)
  obtain ⟨t₁, t₂, t₃, h₁, h₂, hT⟩ := isometric_diag_pivot h2 (mul_ne_zero h2 he)
    (b := 0) (c := 0) (d := e) (e := 0) (f := 0)
    (by rintro ⟨-, h3, -⟩; exact he (by simpa using h3))
  refine ⟨t₁, t₂, t₃, h₁, h₂, (((isometric_shear21 0 0 0 0 e 0 1).of_eq ?_).trans
    (isometric_swap01 _ _ _ _ _ _)).trans hT⟩
  congr 1 <;> ring

end Field

/-! ### Hyperbolic splitting over a finite field -/

section FiniteField

variable {F : Type*} [Field F]

/-- `H ⊥ H ⊥ ⟨δ⟩`, where `H = [[0, 1], [1, 0]]` is the hyperbolic plane: over a finite field
of odd characteristic, the unimodular quinary of determinant `δ` up to squares. -/
def splitForm (δ : F) : Matrix (Fin 5) (Fin 5) F :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, δ]

/-- Over a finite field of odd order, `α x² + β y²` takes every value. -/
theorem exists_sq_add [Fintype F] (hF : Fintype.card F % 2 = 1) {α β : F} (hα : α ≠ 0)
    (hβ : β ≠ 0) (γ : F) : ∃ x y : F, α * x ^ 2 + β * y ^ 2 = γ := by
  have hg : (Polynomial.C β * Polynomial.X ^ 2 - Polynomial.C γ).degree = 2 := by
    rw [Polynomial.degree_sub_C (by rw [Polynomial.degree_C_mul_X_pow 2 hβ]; norm_num),
      Polynomial.degree_C_mul_X_pow 2 hβ]
    rfl
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C α * Polynomial.X ^ 2) (Polynomial.degree_C_mul_X_pow 2 hα) hg hF
  exact ⟨x, y, by simp at h; linear_combination h⟩

/-- Over a finite field of odd order, a nondegenerate binary form takes every value. -/
theorem exists_binary [Fintype F] (hF : Fintype.card F % 2 = 1) {p q r : F} (hp : p ≠ 0)
    (hd : p * r - q ^ 2 ≠ 0) (γ : F) : ∃ μ ν : F, p * μ ^ 2 + 2 * q * μ * ν + r * ν ^ 2 = γ := by
  obtain ⟨x, y, h⟩ := exists_sq_add hF hp (div_ne_zero hd hp) γ
  refine ⟨x - q * y / p, y, ?_⟩
  rw [← h]
  field_simp
  ring

/-- The basis of `hostForm α p q r` adapted to `H ⊥ H ⊥ ⟨α (pr - q²)⟩`: an isotropic vector
`(a, b, 1)` of `⟨1, 1, α⟩` with a dual isotropic vector, then an isotropic vector of the
complement `⟨-α⟩ ⊥ [[p, q], [q, r]]` with its dual, then the complement. -/
def splitBasis (α p q r a b μ ν : F) : Matrix (Fin 5) (Fin 5) F :=
  !![a, -a / (2 * α), b, -b / (2 * α), 0;
     b, -b / (2 * α), -a, a / (2 * α), 0;
     1, 1 / (2 * α), 0, 0, 0;
     0, 0, μ, μ / (2 * α), -(q * μ + r * ν);
     0, 0, ν, ν / (2 * α), p * μ + q * ν]

theorem splitBasis_spec (h2 : (2 : F) ≠ 0) {α p q r a b μ ν : F} (hα : α ≠ 0)
    (hab : a ^ 2 + b ^ 2 = -α) (hμ : p * μ ^ 2 + 2 * q * μ * ν + r * ν ^ 2 = α) :
    (splitBasis α p q r a b μ ν)ᵀ * hostForm α p q r * splitBasis α p q r a b μ ν =
      splitForm (α * (p * r - q ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitBasis, hostForm, splitForm, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;>
    first
    | ring1
    | linear_combination hab
    | linear_combination -hab
    | linear_combination hab + hμ
    | linear_combination -hab + hμ
    | linear_combination (p * r - q ^ 2) * hμ

/-- **Hyperbolic splitting.** Over a finite field of odd order, `hostForm α p q r` contains
`splitForm (α (pr - q²)) = H ⊥ H ⊥ ⟨α (pr - q²)⟩`. -/
theorem exists_splitForm [Fintype F] (hF : Fintype.card F % 2 = 1) (h2 : (2 : F) ≠ 0)
    {α p q r : F} (hα : α ≠ 0) (hp : p ≠ 0) (hd : p * r - q ^ 2 ≠ 0) :
    ∃ P : Matrix (Fin 5) (Fin 5) F,
      Pᵀ * hostForm α p q r * P = splitForm (α * (p * r - q ^ 2)) := by
  obtain ⟨a, b, hab⟩ := exists_sq_add hF one_ne_zero one_ne_zero (-α)
  obtain ⟨μ, ν, hμ⟩ := exists_binary hF hp hd α
  exact ⟨splitBasis α p q r a b μ ν,
    splitBasis_spec (a := a) (b := b) h2 hα (by linear_combination hab) hμ⟩

/-! ### Seeds in `H ⊥ H ⊥ ⟨δ⟩` -/

/-- A seed in `splitForm δ` for `diag(t₁, t₂, t₃)` with `t₁, t₂ ≠ 0`: the first two vectors lie in
the two hyperbolic planes, the third in the complement of the first two and has a unit
coordinate on the line `⟨δ⟩`. -/
theorem seed_splitForm_diag [Fintype F] (hF : Fintype.card F % 2 = 1) (h2 : (2 : F) ≠ 0)
    {δ t₁ t₂ : F} (hδ : δ ≠ 0) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (t₃ : F) :
    Seed (splitForm δ) (ternMat t₁ 0 t₂ 0 0 t₃) := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add hF (neg_ne_zero.mpr h₁) (neg_ne_zero.mpr h₂) (t₃ - δ)
  refine ⟨!![1, 0, x; t₁ / 2, 0, -(x * t₁ / 2); 0, 1, y; 0, t₂ / 2, -(y * t₂ / 2); 0, 0, 1],
    !![1 / t₁, 1 / 2, 0, 0, 0; 0, 0, 1 / t₂, 1 / 2, 0; 0, 0, 0, 0, 1 / δ], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitForm, ternMat, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;>
      first
      | ring1
      | linear_combination hxy
      | linear_combination 2 * hxy
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [splitForm, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring1

/-- A seed in `splitForm δ` for `⟨δ v²⟩ ⊥ B`, `v ≠ 0`, for an arbitrary binary `B`: the first
vector lies on the line `⟨δ⟩` and `B` embeds in `H ⊥ H`. -/
theorem seed_splitForm_line (h2 : (2 : F) ≠ 0) {δ v : F} (hδ : δ ≠ 0) (hv : v ≠ 0) (r s w : F) :
    Seed (splitForm δ) (ternMat (δ * v ^ 2) 0 r 0 s w) := by
  refine ⟨!![0, 1, 0; 0, r / 2, s; 0, 0, 1; 0, 0, w / 2; v, 0, 0],
    !![0, 0, 0, 0, 1 / (δ * v); 0, 1, 0, 0, 0; 0, 0, 0, 1, 0], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitForm, ternMat, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [splitForm, Matrix.mul_apply, Fin.sum_univ_succ]
    field_simp

/-! ### The criteria of `lem:functional` over the field -/

/-- **Rank criterion.** Over a finite field of odd order, a nondegenerate `hostForm α p q r`
has a seed for every ternary of rank at least 2. -/
theorem seed_hostForm_of_rank [Fintype F] (hF : Fintype.card F % 2 = 1) (h2 : (2 : F) ≠ 0)
    {α p q r : F} (hα : α ≠ 0) (hp : p ≠ 0) (hd : p * r - q ^ 2 ≠ 0) {a b c d e f : F}
    (h : RankTwo a b c d e f) : Seed (hostForm α p q r) (ternMat a b c d e f) := by
  obtain ⟨P, hP⟩ := exists_splitForm hF h2 hα hp hd
  obtain ⟨t₁, t₂, t₃, h₁, h₂, hT⟩ := exists_diag h2 h
  exact Seed.of_host P hP
    (Seed.of_isometric hT (seed_splitForm_diag hF h2 (mul_ne_zero hα hd) h₁ h₂ t₃))

/-- **Square class criterion.** Over a finite field of odd order, a nondegenerate
`hostForm α p q r` has a seed for every ternary with a diagonal entry in the square class of
its determinant `α (pr - q²)`. -/
theorem seed_hostForm_of_square [Fintype F] (hF : Fintype.card F % 2 = 1) (h2 : (2 : F) ≠ 0)
    {α p q r : F} (hα : α ≠ 0) (hp : p ≠ 0) (hd : p * r - q ^ 2 ≠ 0) {a b c d e f u : F}
    (hu : u ≠ 0)
    (h : a = α * (p * r - q ^ 2) * u ^ 2 ∨ c = α * (p * r - q ^ 2) * u ^ 2 ∨
      f = α * (p * r - q ^ 2) * u ^ 2) :
    Seed (hostForm α p q r) (ternMat a b c d e f) := by
  obtain ⟨P, hP⟩ := exists_splitForm hF h2 hα hp hd
  refine Seed.of_host P hP ?_
  have hδ : α * (p * r - q ^ 2) ≠ 0 := mul_ne_zero hα hd
  have key : ∀ a b c d e f : F, a = α * (p * r - q ^ 2) * u ^ 2 →
      Seed (splitForm (α * (p * r - q ^ 2))) (ternMat a b c d e f) := by
    intro a b c d e f ha
    have ha0 : a ≠ 0 := ha ▸ mul_ne_zero hδ (pow_ne_zero 2 hu)
    refine Seed.of_isometric (isometric_split ha0 b c d e f) ?_
    rw [ha]
    exact seed_splitForm_line h2 hδ hu _ _ _
  rcases h with h | h | h
  · exact key a b c d e f h
  · exact Seed.of_isometric (isometric_swap01 a b c d e f) (key c b a e d f h)
  · exact Seed.of_isometric (isometric_swap02 a b c d e f) (key f e c d b a h)

end FiniteField

/-! ### Reduction modulo `p` -/

section Reduction

/-- An integer not divisible by `p` is nonzero in `ZMod p`. -/
theorem intCast_ne_zero_of_not_dvd {p : ℕ} {x : ℤ} (h : ¬ (p : ℤ) ∣ x) : (x : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- `ZMod p` has odd order for an odd prime `p`. -/
theorem card_zmod_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : Fintype.card (ZMod p) % 2 = 1 := by
  rw [ZMod.card]
  exact Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)

/-- Rank at least 2 modulo `p`, read in `ZMod p`. -/
theorem rankTwo_of_rankGeTwoMod {p : ℕ} {g : Tern} (h : g.RankGeTwoMod p) :
    RankTwo (g.a : ZMod p) g.b g.c g.d g.e g.f := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  apply h
  intro m hm
  simp only [Tern.minors, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] <;> push_cast <;> assumption

/-- **Hensel's lemma for the hosts.** At an odd prime `p`, a seed modulo `p` for the
reduction of `g` in the reduction of `hostForm α s q r` gives a local representation. -/
theorem locallyRepresents_hostForm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α s q r : ℤ}
    {g : Tern}
    (h : Seed (hostForm (α : ZMod p) s q r) (ternMat (g.a : ZMod p) g.b g.c g.d g.e g.f)) :
    LocallyRepresents (hostForm α s q r) g.toMatrix p := by
  have := Fact.mk hp
  refine locallyRepresents_of_seed hp2 (hostForm_transpose _ _ _ _) g.toMatrix_transpose ?_
  rw [map_hostForm _ (map_zero _) (map_one _), Tern.toMatrix_eq_ternMat, map_ternMat]
  simpa only [eq_intCast] using h

end Reduction

section Hosts

variable {ι : Type*} [Fintype ι] {K : Matrix ι ι ℤ} {e : Matrix ι (Fin 5) ℤ} {α s q r : ℤ}

/-- **The rank criterion of `lem:functional`** at `p ≥ 5`, for a host `K ⊇ hostForm α s q r`
whose invariants `α, s, sr - q²` lie among `1, 2, 3, 4, 6, 9`, so that `p` divides none of
them. -/
theorem rank_of_hostForm (he : eᵀ * K * e = hostForm α s q r)
    (hs : ∀ n ∈ [2, α, s, s * r - q ^ 2], n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 9) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ g : Tern, g.RankGeTwoMod p →
      LocallyRepresents K g.toMatrix p := fun p hp h5 _ hg => by
  have := Fact.mk hp
  have hne : p ≠ 2 := by omega
  have h n (hn : n ∈ [2, α, s, s * r - q ^ 2]) : (n : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_not_dvd (not_dvd_small hp h5 (hs n hn))
  exact .of_host e he <| locallyRepresents_hostForm hp hne <| seed_hostForm_of_rank
    (card_zmod_odd hne) (by exact_mod_cast h 2 (by simp)) (h α (by simp)) (h s (by simp))
    (by exact_mod_cast h _ (by simp)) (rankTwo_of_rankGeTwoMod hg)

/-- **The square class criterion of `lem:functional`** at `p ≥ 5`, for a host
`K ⊇ hostForm α s q r` of determinant `j = α (sr - q²)` whose invariants `α, s, sr - q²` lie
among `1, 2, 3, 4, 6, 9`. -/
theorem square_of_hostForm {j : ℤ} (he : eᵀ * K * e = hostForm α s q r)
    (hs : ∀ n ∈ [2, α, s, s * r - q ^ 2], n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 9)
    (hj : α * (s * r - q ^ 2) = j) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ g : Tern, g.HasDiagSquareClass j p →
      LocallyRepresents K g.toMatrix p := fun p hp h5 _ hg => by
  have := Fact.mk hp
  have hne : p ≠ 2 := by omega
  have h n (hn : n ∈ [2, α, s, s * r - q ^ 2]) : (n : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_not_dvd (not_dvd_small hp h5 (hs n hn))
  obtain ⟨u, hu, hg⟩ := hg
  have key (x : ℤ) (hx : (p : ℤ) ∣ x - j * u ^ 2) :
      (x : ZMod p) = α * (s * r - q ^ 2) * u ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hj] at hx
    push_cast at hx
    linear_combination hx
  refine .of_host e he <| locallyRepresents_hostForm hp hne <| seed_hostForm_of_square
    (card_zmod_odd hne) (by exact_mod_cast h 2 (by simp)) (h α (by simp)) (h s (by simp))
    (by exact_mod_cast h _ (by simp)) (intCast_ne_zero_of_not_dvd hu) ?_
  rcases hg with h | h | h
  exacts [Or.inl (key _ h), Or.inr (Or.inl (key _ h)), Or.inr (Or.inr (key _ h))]

end Hosts

end KimKimOh.Local.OddPrime

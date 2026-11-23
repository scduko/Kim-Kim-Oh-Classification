import KimKimOh.Hosts
import KimKimOh.Maximal
import KimKimOh.Reduced
import KimKimOh.Hosts
import KimKimOh.Maximal
import KimKimOh.Ternary
import KimKimOh.SmallPrimes
import Mathlib.Tactic.FieldSimp

/-!
# The correction `C = G - s λλᵀ` (`eq:highcost`, `eq:sectionbound`)

Both ternary proofs prescribe an integral linear form `λ = (x, y, k)` on the line `⟨s⟩` of
`K_j ⊥ ⟨s⟩ ⊆ L_i` and represent the corrected matrix `G - s λλᵀ` by `K_j`. This file collects
the algebra of the correction used in §§3–4.

* `Tern.corr g s x y k` is `G - s λλᵀ` in coordinates.
* Its leading minors: `a - s x²` (`corr_a`) and `Δ = det(B - s ααᵀ) = δ - s αᵀ adj(B) α`
  (`corrDelta`, `corr_delta`), independent of `k`.
* In Gram–Schmidt form, `det(G - s λλᵀ) = D - s λᵀ adj(G) λ` (`det_corr_eq`) with
  `δ · λᵀ adj(G) λ = D · αᵀ adj(B) α + w²` (`delta_mul_adjForm`) and
  `a · αᵀ adj(B) α = δ x² + (a y - b x)²` (`a_mul_binForm`).
* The correction has rank at least 2 at every prime not dividing `Δ` (`rankGeTwoMod_corr`).
* `Tern.posDef_of_minors`: a symmetric ternary with positive leading minors `a, δ, D` is
  positive definite (Sylvester's criterion in rank 3, from `G = Uᵀ diag(a, δ/a, D/δ) U`).
* `Tern.corr_pos_of_adjForm`: the correction is positive as soon as `s λᵀ adj(G) λ < D`, that
  is `s λᵀ G⁻¹ λ < 1` (`eq:highcost`); `exists_window` gives positive corrections on terms of a
  progression in `k` near the centre `αᵀ B⁻¹ r` of the interval of `k`.
* `represents_of_corr`: if the correction is positive and `K` represents it at every prime,
  then, by the local–global input for `K`, the lattice `K ⊥ ⟨s⟩` represents `G`.
-/

namespace KimKimOh

open Matrix GramLattice

namespace Tern

/-- The corrected ternary `G - s λλᵀ` for `λ = (x, y, k)`. -/
def corr (g : Tern) (s x y k : ℤ) : Tern :=
  ⟨g.a - s * x * x, g.b - s * x * y, g.c - s * y * y, g.d - s * x * k, g.e - s * y * k,
    g.f - s * k * k⟩

theorem corr_toMatrix (g : Tern) (s x y k : ℤ) :
    (g.corr s x y k).toMatrix = g.toMatrix - s • vecMulVec ![x, y, k] ![x, y, k] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corr, toMatrix, vecMulVec] <;> ring

/-! ### Leading minors and the determinant -/

theorem corr_a (g : Tern) (s x y k : ℤ) : (g.corr s x y k).a = g.a - s * x * x := rfl

/-- The value `αᵀ adj(B) α` at `α = (x, y)`. -/
def binForm (g : Tern) (x y : ℤ) : ℤ := g.c * x * x - 2 * g.b * x * y + g.a * y * y

/-- `Δ = det(B - s ααᵀ)`, the leading binary minor of the correction. -/
def corrDelta (g : Tern) (s x y : ℤ) : ℤ :=
  g.delta - s * (g.c * x * x - 2 * g.b * x * y + g.a * y * y)

theorem corrDelta_eq (g : Tern) (s x y : ℤ) : g.corrDelta s x y = g.delta - s * g.binForm x y :=
  rfl

theorem corr_delta (g : Tern) (s x y k : ℤ) : (g.corr s x y k).delta = g.corrDelta s x y := by
  simp only [corr, delta, corrDelta]; ring

/-- `τ = αᵀ adj(B) r`: the centre `αᵀ B⁻¹ r` of the interval of `k` with `C > 0` is `τ / δ`. -/
def tau (g : Tern) (x y : ℤ) : ℤ :=
  -(x * (g.b * g.e - g.c * g.d) + y * (g.b * g.d - g.a * g.e))

/-- The value `λᵀ adj(G) λ` at `λ = (x, y, z)`. -/
def adjForm (g : Tern) (x y z : ℤ) : ℤ :=
  (g.c * g.f - g.e * g.e) * x * x + (g.a * g.f - g.d * g.d) * y * y + g.delta * z * z +
    2 * ((g.d * g.e - g.b * g.f) * x * y + (g.b * g.e - g.c * g.d) * x * z +
      (g.b * g.d - g.a * g.e) * y * z)

/-- `w = δ z - (ae - bd) y - (cd - be) x`, `δ` times the last Gram–Schmidt coordinate. -/
def wlin (g : Tern) (x y z : ℤ) : ℤ :=
  g.delta * z - (g.a * g.e - g.b * g.d) * y - (g.c * g.d - g.b * g.e) * x

theorem det_corr_eq (g : Tern) (s x y z : ℤ) :
    (g.corr s x y z).det = g.det - s * g.adjForm x y z := by
  simp only [det, delta, corr, adjForm]; ring

theorem delta_mul_adjForm (g : Tern) (x y z : ℤ) :
    g.delta * g.adjForm x y z = g.det * g.binForm x y + g.wlin x y z ^ 2 := by
  simp only [delta, det, adjForm, binForm, wlin]; ring

theorem a_mul_binForm (g : Tern) (x y : ℤ) :
    g.a * g.binForm x y = g.delta * x ^ 2 + (g.a * y - g.b * x) ^ 2 := by
  simp only [delta, binForm]; ring

/-- `Δ ≤ δ`: the subtracted form `s αᵀ adj(B) α` is nonnegative. -/
theorem corrDelta_le (g : Tern) (s x y : ℤ) (hs : 0 ≤ s) (ha : 0 < g.a) (hδ : 0 < g.delta) :
    g.corrDelta s x y ≤ g.delta := by
  have hq : 0 ≤ g.binForm x y :=
    (mul_nonneg_iff_of_pos_left ha).mp (by rw [a_mul_binForm]; positivity)
  rw [corrDelta_eq]
  nlinarith

/-! ### Residues -/

/-- At a prime not dividing `Δ` the correction has rank at least 2. -/
theorem rankGeTwoMod_corr (g : Tern) (s x y k : ℤ) {p : ℕ} (h : ¬ (p : ℤ) ∣ g.corrDelta s x y) :
    (g.corr s x y k).RankGeTwoMod p := fun hle =>
  h (by simpa [minors, ← corr_delta g s x y k, delta] using hle _ (List.mem_cons_self))

/-! ### Positivity -/

/-- **Sylvester's criterion in rank 3.** A symmetric ternary integer matrix with positive
leading minors `a`, `δ = ac - b²` and `D = det` is positive definite. -/
theorem posDef_of_minors (g : Tern) (ha : 0 < g.a) (hδ : 0 < g.delta) (hD : 0 < g.det) :
    (g.toMatrix.map (Int.cast : ℤ → ℝ)).PosDef := by
  have ha' : (0 : ℝ) < g.a := by exact_mod_cast ha
  have hδ' : (0 : ℝ) < g.delta := by exact_mod_cast hδ
  have hD' : (0 : ℝ) < g.det := by exact_mod_cast hD
  have ha0 : (g.a : ℝ) ≠ 0 := ha'.ne'
  have hδ0 : (g.delta : ℝ) ≠ 0 := hδ'.ne'
  set u₁ : ℝ := g.b / g.a
  set u₂ : ℝ := g.d / g.a
  set u₃ : ℝ := (g.a * g.e - g.b * g.d) / g.delta
  have hδdef : (g.delta : ℝ) = g.a * g.c - g.b * g.b := by simp [delta]
  have hDdef : (g.det : ℝ) = g.delta * g.f - g.c * g.d * g.d + 2 * g.b * g.d * g.e -
      g.a * g.e * g.e := by simp [det]
  refine posDef_of_ldl (d := ![(g.a : ℝ), g.delta / g.a, g.det / g.delta])
    (U := Matrix.of ![![1, u₁, u₂], ![0, 1, u₃], ![0, 0, 1]])
    (V := Matrix.of ![![1, -u₁, u₁ * u₃ - u₂], ![0, 1, -u₃], ![0, 0, 1]]) ?_ ?_ ?_
  · intro i; fin_cases i <;> simp <;> positivity
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]; ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix, Matrix.mul_apply, Fin.sum_univ_three, diagonal, u₁, u₂, u₃] <;>
      field_simp <;> (try simp only [hDdef]) <;> (try simp only [hδdef]) <;> ring

/-- **Positivity of the correction.** If `a, δ, D > 0` and `s λᵀ adj(G) λ < D` with `s ≥ 0`, then
the corrected ternary has positive leading minors. -/
theorem corr_pos_of_adjForm (g : Tern) {s x y z : ℤ} (ha : 0 < g.a) (hδ : 0 < g.delta)
    (hD : 0 < g.det) (hs : 0 ≤ s) (h : s * g.adjForm x y z < g.det) :
    0 < (g.corr s x y z).a ∧ 0 < (g.corr s x y z).delta ∧ 0 < (g.corr s x y z).det := by
  have h1 := g.delta_mul_adjForm x y z
  have h2 := g.a_mul_binForm x y
  have hD' : 0 < (g.corr s x y z).det := by rw [det_corr_eq]; linarith
  have hw : 0 ≤ s * g.wlin x y z ^ 2 := by positivity
  have hb2 : 0 ≤ s * (g.a * y - g.b * x) ^ 2 := by positivity
  -- `δ · D' ≤ D · δ'`
  have hδ' : 0 < (g.corr s x y z).delta := by
    rw [corr_delta, corrDelta_eq]
    have key : g.delta * (g.det - s * g.adjForm x y z) =
        g.det * (g.delta - s * g.binForm x y) - s * g.wlin x y z ^ 2 := by
      linear_combination (-s) * h1
    have : 0 < g.det * (g.delta - s * g.binForm x y) := by
      have : 0 < g.delta * (g.det - s * g.adjForm x y z) := mul_pos hδ (by linarith)
      linarith
    exact pos_of_mul_pos_right this hD.le
  have ha' : 0 < (g.corr s x y z).a := by
    rw [corr_a]
    have key : g.a * (g.delta - s * g.binForm x y) =
        g.delta * (g.a - s * x * x) - s * (g.a * y - g.b * x) ^ 2 := by
      linear_combination (-s) * h2
    have hpos : 0 < g.a * (g.delta - s * g.binForm x y) := by
      rw [corr_delta, corrDelta_eq] at hδ'; exact mul_pos ha hδ'
    have : 0 < g.delta * (g.a - s * x * x) := by linarith
    exact pos_of_mul_pos_right this hδ.le
  exact ⟨ha', hδ', hD'⟩

end Tern

/-! ### The positivity window -/

/-- **The window of positive corrections** (`eq:highcost`, `eq:sectionbound`). If `a, δ, D > 0` and
`s (M len)² δ² < 4 D Δ`, then in every class `r` modulo `M > 0` the corrections are positive
for the `len` terms `k₀ + M t`, `t < len`, nearest the centre `τ/δ`. -/
theorem exists_window (g : Tern) (ha : 0 < g.a) (hδ : 0 < g.delta) (hD : 0 < g.det)
    {s x y : ℤ} (hs : 0 < s) {M : ℤ} (hM : 0 < M) (r : ℤ) (len : ℕ)
    (hcert : s * (M * len) ^ 2 * g.delta ^ 2 < 4 * g.det * g.corrDelta s x y) :
    ∃ k₀ : ℤ, M ∣ k₀ - r ∧ ∀ t : ℕ, t < len → 0 < (g.corr s x y (k₀ + M * t)).a ∧
      0 < (g.corr s x y (k₀ + M * t)).delta ∧ 0 < (g.corr s x y (k₀ + M * t)).det := by
  obtain ⟨k₀, hr, hk⟩ := exists_centred_progression (B := 2 * g.tau x y) hδ hM r len
  refine ⟨k₀, hr, fun t ht => g.corr_pos_of_adjForm ha hδ hD hs.le ?_⟩
  -- `|2 w| ≤ M len δ` for `w = δ k - τ`, and `δ · λᵀ adj(G) λ = D · αᵀ adj(B) α + w²`
  have hsq : (2 * g.wlin x y (k₀ + M * t)) ^ 2 ≤ (M * len * g.delta) ^ 2 := by
    rw [← sq_abs, show 2 * g.wlin x y (k₀ + M * t) = 2 * g.delta * (k₀ + M * t) - 2 * g.tau x y
      by simp only [Tern.wlin, Tern.tau]; ring]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [hk t ht]) 2
  have h1 := g.delta_mul_adjForm x y (k₀ + M * t)
  rw [Tern.corrDelta_eq] at hcert
  exact lt_of_mul_lt_mul_left (a := g.delta)
    (by nlinarith [mul_le_mul_of_nonneg_left hsq hs.le]) hδ.le

/-- The ternary lattice with the given entries, when its leading minors are positive. -/
def Tern.toLattice (g : Tern) (ha : 0 < g.a) (hδ : 0 < g.delta) (hD : 0 < g.det) :
    GramLattice (Fin 3) :=
  ⟨g.toMatrix, g.posDef_of_minors ha hδ hD⟩

/-- **The correction step with the local–global input.** If `G - s λλᵀ` has positive
leading minors and the host `K` represents it at every prime, and `K` satisfies the
local–global principle for ternaries, then `K ⊥ ⟨s⟩` represents `G`. -/
theorem represents_of_corr {κ : Type*} [Fintype κ] (K : GramLattice κ)
    (hK : ∀ S : GramLattice (Fin 3),
      (∀ p : ℕ, p.Prime → LocallyRepresents K.gram S.gram p) → K.Represents S)
    {s : ℤ} (hs : 0 < s) (S : GramLattice (Fin 3)) (x y k : ℤ)
    (ha : 0 < ((ternOf S).corr s x y k).a) (hδ : 0 < ((ternOf S).corr s x y k).delta)
    (hD : 0 < ((ternOf S).corr s x y k).det)
    (hloc : ∀ p : ℕ, p.Prime →
      LocallyRepresents K.gram ((ternOf S).corr s x y k).toMatrix p) :
    (K.orthSum (line s hs)).Represents S := by
  obtain ⟨Y, hY⟩ := hK (((ternOf S).corr s x y k).toLattice ha hδ hD) hloc
  refine represents_orthSum_line K hs S ![x, y, k] Y ?_
  rw [hY]
  change ((ternOf S).corr s x y k).toMatrix = _
  rw [Tern.corr_toMatrix, ternOf_toMatrix]

end KimKimOh

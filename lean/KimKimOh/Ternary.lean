import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Ternary Gram matrices in the coordinates of §3

`Tern` records a symmetric ternary integer matrix
```
G = [[a, b, d],
     [b, c, e],
     [d, e, f]]
```
in the notation of §3 of the paper: `B = [[a, b], [b, c]]` is the leading binary section,
`r = (r₁, r₂) = (d, e)`, `δ = ac - b²` and `D = det G`.

The file defines the quantities that the paper's propositions refer to:

* `Tern.det`, `Tern.delta`, the 2×2 minors `Tern.minors`, `Tern.RankLeOneMod p`
  (rank at most 1 modulo `p`) and `Tern.NonzeroMod p` (`G ≢ 0 (mod p)`);
* `Tern.IsReduced`: the inequalities of §3 (`eq:lengths`) of a size-reduced Korkine–Zolotarev basis
  together with the Gram–Schmidt bounds used in §3.
-/

namespace KimKimOh

/-- A symmetric ternary integer matrix with rows `(a, b, d)`, `(b, c, e)`, `(d, e, f)`. -/
@[ext] structure Tern where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  deriving DecidableEq, Repr

namespace Tern

variable (g : Tern)

/-- The matrix of `g`. -/
def toMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![![g.a, g.b, g.d], ![g.b, g.c, g.e], ![g.d, g.e, g.f]]

/-- The entries of a ternary matrix (its upper triangle). -/
def ofMatrix (G : Matrix (Fin 3) (Fin 3) ℤ) : Tern :=
  ⟨G 0 0, G 0 1, G 1 1, G 0 2, G 1 2, G 2 2⟩

theorem toMatrix_ofMatrix {G : Matrix (Fin 3) (Fin 3) ℤ} (hG : G.IsSymm) :
    (ofMatrix G).toMatrix = G := by
  have h (i j : Fin 3) : G j i = G i j := congrFun (congrFun hG i) j
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, ofMatrix] <;> exact h _ _

@[simp] theorem ofMatrix_toMatrix : ofMatrix g.toMatrix = g := by
  cases g; rfl

/-- `δ = ac - b²`, the determinant of the leading binary section. -/
def delta : ℤ := g.a * g.c - g.b * g.b

/-- `D = det G`. -/
def det : ℤ :=
  g.delta * g.f - g.c * g.d * g.d + 2 * g.b * g.d * g.e - g.a * g.e * g.e

theorem det_toMatrix : g.toMatrix.det = g.det := by
  simp [toMatrix, Matrix.det_fin_three, det, delta]; ring

/-- The six 2×2 minors, principal ones first, in the order of the paper's verifier. -/
def minors : List ℤ :=
  [g.a * g.c - g.b * g.b, g.a * g.f - g.d * g.d, g.c * g.f - g.e * g.e,
   g.a * g.e - g.b * g.d, g.b * g.e - g.c * g.d, g.b * g.f - g.d * g.e]

/-- `G` has rank at most 1 modulo `p`: every 2×2 minor is divisible by `p`. -/
def RankLeOneMod (p : ℕ) : Prop :=
  ∀ m ∈ g.minors, (p : ℤ) ∣ m

/-- `G` has rank at least 2 modulo `p`: some 2×2 minor is not divisible by `p`. -/
def RankGeTwoMod (p : ℕ) : Prop := ¬ g.RankLeOneMod p

/-- Some diagonal entry of `G` is `j u²` modulo `p` for a unit `u`. -/
def HasDiagSquareClass (j : ℤ) (p : ℕ) : Prop :=
  ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
    ((p : ℤ) ∣ g.a - j * u ^ 2 ∨ (p : ℤ) ∣ g.c - j * u ^ 2 ∨ (p : ℤ) ∣ g.f - j * u ^ 2)

/-- `G ≢ 0 (mod p)`: some entry is not divisible by `p`. -/
def NonzeroMod (p : ℕ) : Prop :=
  ¬ ((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c ∧ (p : ℤ) ∣ g.d ∧ (p : ℤ) ∣ g.e ∧
    (p : ℤ) ∣ g.f)

/-- The value `xᵀ G x` at `x = (x, y, z)`. -/
def eval (x y z : ℤ) : ℤ :=
  g.a * x * x + g.c * y * y + g.f * z * z + 2 * (g.b * x * y + g.d * x * z + g.e * y * z)

/-- The inequalities satisfied by the Gram matrix of a size-reduced Korkine–Zolotarev basis
(§3): `a` is the minimum, `0 ≤ 2b ≤ a ≤ c`, the Gram–Schmidt coefficients `μ₃₁ = d/a` and
`μ₃₂ = (ae - bd)/δ` lie in `[-1/2, 1/2]`, the projection of the third vector away from the
first has squared length at least `β = δ/a`, and `γ = D/δ ≥ 3β/4`. -/
structure IsReduced : Prop where
  b_nonneg : 0 ≤ g.b
  two_b_le_a : 2 * g.b ≤ g.a
  a_le_c : g.a ≤ g.c
  two_d_le : 2 * |g.d| ≤ g.a
  two_mu_le : 2 * |g.a * g.e - g.b * g.d| ≤ g.delta
  a_le_f : g.a ≤ g.f
  delta_le_proj : g.delta ≤ g.a * g.f - g.d * g.d
  height : 3 * g.delta ^ 2 ≤ 4 * g.a * g.det
  a_le_eval : ∀ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) → g.a ≤ g.eval x y z

end Tern

end KimKimOh

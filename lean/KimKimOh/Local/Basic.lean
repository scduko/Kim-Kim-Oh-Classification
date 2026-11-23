import KimKimOh.Hosts
import KimKimOh.Maximal
import KimKimOh.Ternary
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Prime.Int
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Local representations and the shape of the hosts

The tools of §2 used at every prime.

* **Ternary matrices.** `ternMat a b c d e f` is the symmetric matrix with the entries of `Tern`,
  over any ring.
* **Local representations.** `LocallyRepresents K S p`, congruences `Xᵀ K X ≡ S (mod pᵏ)` for
  every `k`, follows from an exact representation (`locallyRepresents_of_eq`) and is transitive
  (`LocallyRepresents.trans`). Hence a local representation by a sublattice `Qᵀ K Q` of `K` is one
  by `K` (`LocallyRepresents.of_host`).
* **The quinary lattices.** `K₃` and `K₉` have the shape
  `hostForm α a q r = ⟨1, 1, α⟩ ⊥ [[a, q], [q, r]]`, with `α = 1` and `α = 3` and binary part
  `A₂` (`K3_embed`, `K9_embed`, which only reorder the bases).
-/

namespace KimKimOh.Local

open Matrix

variable {ι κ μ ν : Type*}

/-- If every entry of `E` is divisible by `n`, so is every entry of `A * E * B`. -/
theorem dvd_mul_mul_apply [Fintype ι] [Fintype κ] {n : ℤ} (A : Matrix μ ι ℤ)
    (E : Matrix ι κ ℤ) (B : Matrix κ ν ℤ) (hE : ∀ i j, n ∣ E i j) (i : μ) (j : ν) :
    n ∣ (A * E * B) i j := by
  simp only [Matrix.mul_apply]
  refine Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (Finset.dvd_sum fun m _ => ?_) _
  exact dvd_mul_of_dvd_right (hE m l) _

/-! ### Ternary matrices -/

section TernMat

variable {R S : Type*}

/-- The symmetric matrix `[[a, b, d], [b, c, e], [d, e, f]]`, with the entries in the order
of `Tern`. -/
def ternMat (a b c d e f : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a, b, d; b, c, e; d, e, f]

theorem ternMat_transpose (a b c d e f : R) : (ternMat a b c d e f)ᵀ = ternMat a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem map_ternMat (φ : R → S) (a b c d e f : R) :
    (ternMat a b c d e f).map φ = ternMat (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end TernMat

end KimKimOh.Local

namespace KimKimOh

open Matrix Local

variable {ι κ μ : Type*}

theorem Tern.toMatrix_eq_ternMat (g : Tern) : g.toMatrix = ternMat g.a g.b g.c g.d g.e g.f :=
  rfl

theorem Tern.toMatrix_transpose (g : Tern) : g.toMatrixᵀ = g.toMatrix :=
  ternMat_transpose _ _ _ _ _ _

/-! ### Local representations -/

section LocallyRepresents

variable [Fintype ι]

/-- An exact representation `Yᵀ K Y = M` is a local representation at every prime. -/
theorem locallyRepresents_of_eq {K : Matrix ι ι ℤ} {M : Matrix κ κ ℤ}
    (Y : Matrix ι κ ℤ) (hY : Yᵀ * K * Y = M) (p : ℕ) : LocallyRepresents K M p :=
  fun _ => ⟨Y, fun i j => by simp [hY]⟩

variable [Fintype κ]

/-- Local representations compose. -/
theorem LocallyRepresents.trans [Fintype μ] {K : Matrix ι ι ℤ} {M : Matrix κ κ ℤ}
    {S : Matrix μ μ ℤ} {p : ℕ} (hKM : LocallyRepresents K M p)
    (hMS : LocallyRepresents M S p) : LocallyRepresents K S p := by
  intro k
  obtain ⟨Z, hZ⟩ := hKM k
  obtain ⟨Y, hY⟩ := hMS k
  refine ⟨Z * Y, fun i j => ?_⟩
  have h1 : (Z * Y)ᵀ * K * (Z * Y) = Yᵀ * M * Y + Yᵀ * (Zᵀ * K * Z - M) * Y := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, transpose_mul]
    simp only [Matrix.mul_assoc]
  have h2 := dvd_mul_mul_apply Yᵀ (Zᵀ * K * Z - M) Y (fun a b => by
    simpa [sub_apply] using hZ a b) i j
  rw [h1, Matrix.add_apply, add_sub_right_comm]
  exact dvd_add (hY i j) h2

/-- A local representation by a sublattice `Qᵀ K Q` of `K` is one by `K`. -/
theorem LocallyRepresents.of_host [Fintype μ] {K : Matrix ι ι ℤ} {K' : Matrix μ μ ℤ}
    {T : Matrix κ κ ℤ} {p : ℕ} (Q : Matrix ι μ ℤ) (hQ : Qᵀ * K * Q = K')
    (h : LocallyRepresents K' T p) : LocallyRepresents K T p :=
  (locallyRepresents_of_eq Q hQ p).trans h

end LocallyRepresents

end KimKimOh

/-! ### The hosts -/

namespace KimKimOh.Local

open Matrix

section HostForm

variable {R S : Type*} [Zero R] [One R] [Zero S] [One S]

/-- `⟨1, 1, α⟩ ⊥ [[a, q], [q, r]]`, the shape of `K₃` and `K₉`. -/
def hostForm (α a q r : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, α, 0, 0; 0, 0, 0, a, q; 0, 0, 0, q, r]

theorem hostForm_transpose (α a q r : R) : (hostForm α a q r)ᵀ = hostForm α a q r := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem map_hostForm (φ : R → S) (h0 : φ 0 = 0) (h1 : φ 1 = 1) (α a q r : R) :
    (hostForm α a q r).map φ = hostForm (φ α) (φ a) (φ q) (φ r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hostForm, h0, h1]

end HostForm

/-- The integer matrix sending the `j`-th basis vector of `Fin 5` to the basis vector
`e j`. -/
def embedMat {ι : Type*} [DecidableEq ι] (e : Fin 5 → ι) : Matrix ι (Fin 5) ℤ :=
  Matrix.of fun x j => if x = e j then 1 else 0

/-- The basis of `K₃` in its own order. -/
def hostBasisK3 : Fin 5 → Fin 3 ⊕ Fin 2 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]

/-- The basis of `K₉`, with the line `⟨3⟩` moved to the third position. -/
def hostBasisK9 : Fin 5 → (Fin 2 ⊕ Fin 2) ⊕ Fin 1 :=
  ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1), Sum.inr 0, Sum.inl (Sum.inr 0),
    Sum.inl (Sum.inr 1)]

theorem K3_embed :
    (embedMat hostBasisK3)ᵀ * K3.gram * embedMat hostBasisK3 = hostForm 1 2 (-1) 2 := by decide

theorem K9_embed :
    (embedMat hostBasisK9)ᵀ * K9.gram * embedMat hostBasisK9 = hostForm 3 2 (-1) 2 := by decide

end KimKimOh.Local

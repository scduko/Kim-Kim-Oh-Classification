import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Prime.Basic

/-!
# Maximal lattices and local representations

* `IsMaximal G`: the lattice with Gram matrix `G` has no proper integral enlargement
  (§2, `eq:maximal`). Adjoining `x / p` to the lattice gives an integral lattice exactly when
  `G x ≡ 0 (mod p)` and `xᵀ G x ≡ 0 (mod p²)`, so maximality says that no such `x` with
  `x ≢ 0 (mod p)` exists.
* `LocallyRepresents K S p`: `K` represents `S` over `ℤ_p`, stated by congruences: for
  every `k` some integer matrix `X` has `Xᵀ K X ≡ S (mod pᵏ)`. By compactness of `ℤ_p`
  this is equivalent to `Xᵀ K X = S` for a matrix `X` over `ℤ_p`.
-/

namespace KimKimOh

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `G` is maximal: no prime `p` and integer vector `x ≢ 0 (mod p)` satisfy `G x ≡ 0 (mod p)`
and `xᵀ G x ≡ 0 (mod p²)`. Such an `x` would make `x / p` an integral enlargement. -/
def IsMaximal (G : Matrix ι ι ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ x : ι → ℤ, (∃ i, ¬ (p : ℤ) ∣ x i) →
    (∀ i, (p : ℤ) ∣ (G *ᵥ x) i) → ¬ ((p : ℤ) ^ 2 ∣ x ⬝ᵥ (G *ᵥ x))

/-- `K` represents `S` over `ℤ_p`: for every `k`, some integer matrix `X` satisfies
`Xᵀ K X ≡ S (mod pᵏ)` entrywise. -/
def LocallyRepresents (K : Matrix ι ι ℤ) (S : Matrix κ κ ℤ) (p : ℕ) : Prop :=
  ∀ k : ℕ, ∃ X : Matrix ι κ ℤ, ∀ i j, (p : ℤ) ^ k ∣ (Xᵀ * K * X) i j - S i j

end KimKimOh

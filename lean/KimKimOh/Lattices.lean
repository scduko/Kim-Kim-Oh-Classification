import KimKimOh.GramLattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# The lattices of the paper

* `stdLattice n` is `Iₙ = ⟨1, …, 1⟩`; a lattice representing every lattice of rank `n` is
  `n`-universal (`isUniversal_of_rank`);
* `rootA1 = A₁ = ⟨2⟩`, `lattice3 = ⟨3⟩`, and `rootA2 = A₂`, with Gram matrix
  `[[2, -1], [-1, 2]]` (roots of norm 2 with pairing `-1`; the paper defines `A_r` in §1);
* `L6 = I₃ ⊥ A₁ ⊥ A₂` and `L9 = I₃ ⊥ A₂ ⊥ ⟨3⟩`, the two rank-6 lattices of
  Theorem 1.2(i),(ii), indexed by determinant;
* `I6A2 = I₆ ⊥ A₂`, the rank-8 lattice of Theorem 1.2(iii).

The quinary lattice `Λ₁₁₇` of Proposition 5.1 (`prop:exception`) is `quinaryT` in
`KimKimOh/Quinary.lean`, and the quinary hosts `K_j` of §2 are in `KimKimOh/Hosts.lean`.
-/

namespace KimKimOh

open Matrix GramLattice

/-- The diagonal lattice `⟨d₁, …, dₙ⟩`. -/
def diagLattice {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℤ) (hd : ∀ i, 0 < d i) :
    GramLattice ι where
  gram := diagonal d
  posDef := by
    rw [diagonal_map (Int.cast_zero)]
    exact PosDef.diagonal fun i => by exact_mod_cast hd i

/-- The standard lattice `Iₙ`. -/
def stdLattice (n : ℕ) : GramLattice (Fin n) :=
  diagLattice (fun _ => 1) fun _ => one_pos

/-- **Universality from the top rank.** A lattice that represents every lattice of rank `n` is
`n`-universal: a lattice `S` of rank `m ≤ n` lies in `S ⊥ I_{n-m}`, which has rank `n`. -/
theorem isUniversal_of_rank {ι : Type*} [Fintype ι] (L : GramLattice ι) (n : ℕ)
    (h : ∀ S : GramLattice (Fin n), L.Represents S) : L.IsUniversal n := by
  intro m hm S
  let e : Fin m ⊕ Fin (n - m) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  have hS := h ((S.orthSum (stdLattice (n - m))).reindex e)
  rw [represents_reindex_iff] at hS
  exact hS.trans (represents_orthSum_left S _)

/-- The root lattice `A₁ = ⟨2⟩`. -/
def rootA1 : GramLattice (Fin 1) :=
  diagLattice (fun _ => 2) fun _ => two_pos

/-- The lattice `⟨3⟩`. -/
def lattice3 : GramLattice (Fin 1) :=
  diagLattice (fun _ => 3) fun _ => by norm_num

/-- The root lattice `A₂`, with Gram matrix `[[2, -1], [-1, 2]]`. -/
def rootA2 : GramLattice (Fin 2) where
  gram := Matrix.of ![![2, -1], ![-1, 2]]
  posDef := posDef_of_ldl (d := ![2, 3 / 2]) (U := Matrix.of ![![1, -1 / 2], ![0, 1]])
    (V := Matrix.of ![![1, 1 / 2], ![0, 1]])
    (by intro i; fin_cases i <;> norm_num)
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, diagonal])

/-- `L₆ = I₃ ⊥ A₁ ⊥ A₂`, of determinant 6. -/
def L6 : GramLattice ((Fin 3 ⊕ Fin 1) ⊕ Fin 2) :=
  ((stdLattice 3).orthSum rootA1).orthSum rootA2

/-- `L₉ = I₃ ⊥ A₂ ⊥ ⟨3⟩`, of determinant 9. -/
def L9 : GramLattice ((Fin 3 ⊕ Fin 2) ⊕ Fin 1) :=
  ((stdLattice 3).orthSum rootA2).orthSum lattice3

/-- `I₆ ⊥ A₂`, of rank 8 and determinant 3. -/
def I6A2 : GramLattice (Fin 6 ⊕ Fin 2) :=
  (stdLattice 6).orthSum rootA2

end KimKimOh

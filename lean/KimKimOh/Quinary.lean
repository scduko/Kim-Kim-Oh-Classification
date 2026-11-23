import KimKimOh.Lattices
import KimKimOh.Quinary.Core

/-!
# Theorem 1.2(iii): `I₆ ⊥ A₂` is not 5-universal (`sec:five`)

Proposition 5.1, `prop:exception` (`not_represents_quinaryT`): the lattice `I₆ ⊥ A₂` does not
represent the positive-definite quinary lattice `Λ₁₁₇` of determinant 117 (`quinaryT`). The argument is in
`KimKimOh.Quinary.Core`, at the level of Gram matrices; this file transfers it to
`GramLattice`. It uses no hypotheses.
-/

namespace KimKimOh

open Matrix GramLattice

/-- The quinary lattice `Λ₁₁₇` of Proposition 5.1, of determinant 117. Its leading principal
minors are `2, 3, 4, 21, 117`; positive definiteness is shown by the factorization
`T = Uᵀ diag(2, 3/2, 4/3, 21/4, 39/7) U`. -/
def quinaryT : GramLattice (Fin 5) where
  gram := Quinary.gramT
  posDef := posDef_of_ldl (d := ![2, 3 / 2, 4 / 3, 21 / 4, 39 / 7])
    (U := Matrix.of ![![1, -1 / 2, 0, 1 / 2, 0],
                      ![0, 1, -2 / 3, 1 / 3, 2 / 3],
                      ![0, 0, 1, 1 / 4, 1 / 2],
                      ![0, 0, 0, 1, -2 / 7],
                      ![0, 0, 0, 0, 1]])
    (V := Matrix.of ![![1, 1 / 2, 1 / 3, -3 / 4, -5 / 7],
                      ![0, 1, 2 / 3, -1 / 2, -8 / 7],
                      ![0, 0, 1, -1 / 4, -4 / 7],
                      ![0, 0, 0, 1, 2 / 7],
                      ![0, 0, 0, 0, 1]])
    (by intro i; fin_cases i <;> norm_num)
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_five])
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Quinary.gramT, Matrix.mul_apply, Fin.sum_univ_five, diagonal])

theorem I6A2_gram : I6A2.gram = Quinary.gramL := by
  simp [I6A2, stdLattice, diagLattice, rootA2, Quinary.gramL, Quinary.gramA2]

/-- **Proposition 5.1** (`prop:exception`). `I₆ ⊥ A₂` does not represent `Λ₁₁₇`. -/
theorem not_represents_quinaryT : ¬ I6A2.Represents quinaryT := by
  rintro ⟨X, hX⟩
  rw [I6A2_gram] at hX
  exact Quinary.not_represents X hX

/-- **Theorem 1.2(iii).** `I₆ ⊥ A₂` is not 5-universal. -/
theorem not_isUniversal_I6A2 : ¬ I6A2.IsUniversal 5 :=
  fun h => not_represents_quinaryT (h le_rfl quinaryT)

end KimKimOh

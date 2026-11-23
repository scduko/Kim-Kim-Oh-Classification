import KimKimOh.Overlattice
import KimKimOh.Quinary
import KimKimOh.Statement
import KimKimOh.Hosts
import KimKimOh.Genus.Kko113
import KimKimOh.Genus.Kko112

/-!
# Assembling Theorem 1.2

`isUniversal_three_of_steps` is the skeleton of the proof of Theorem 1.2(i),(ii) (§2):

1. a lattice of rank less than 3 is extended by unit lines
   (`isUniversal_of_rank`);
2. every ternary lies in a maximal ternary, which has a reduced basis
   (`exists_maximal_reduced`);
3. if the minimum is 1, a unit vector splits off, and its complement in `L_i` is
   2-universal by Kim–Kim–Oh (`represents_of_unit`, `L6_represents_of_unit`,
   `L9_represents_of_unit`);
4. the maximal ternaries of minimum at least 2 are §4 (`MinTwo6`, `MinTwo9`).

`mainTheorem_of_minTwo` derives Theorem 1.2 from step 4; part (iii) is `not_isUniversal_I6A2`.
-/

namespace KimKimOh

open Matrix GramLattice

/-! ### Minimum 1 -/

section Unit

/-- The binary lattice spanned by the last two basis vectors of a ternary lattice. -/
def lowerBlock (S : GramLattice (Fin 3)) : GramLattice (Fin 2) :=
  ⟨S.gram.submatrix Fin.succ Fin.succ, by
    simpa [submatrix_map] using S.posDef.submatrix (Fin.succ_injective 2)⟩

/-- **Minimum 1.** If `S = ⟨1⟩ ⊥ S′` in its basis and `K` represents `S′`, then `K ⊥ ⟨1⟩`
represents `S`. This is the correction step (`represents_orthSum_line`) with `s = 1` and
`λ = (1, 0, 0)`: `G - λλᵀ = 0 ⊥ S′`. -/
theorem represents_of_unit {κ : Type*} [Fintype κ] (K : GramLattice κ) (S : GramLattice (Fin 3))
    (h1 : S.gram 0 0 = 1) (h01 : S.gram 0 1 = 0) (h02 : S.gram 0 2 = 0)
    (hK : K.Represents (lowerBlock S)) : (K.orthSum (line 1 one_pos)).Represents S := by
  obtain ⟨Y, hY⟩ := hK
  have h10 : S.gram 1 0 = 0 := by rw [S.gram_comm]; exact h01
  have h20 : S.gram 2 0 = 0 := by rw [S.gram_comm]; exact h02
  have h21 := S.gram_comm 2 1
  let P : Matrix (Fin 2) (Fin 3) ℤ := !![0, 1, 0; 0, 0, 1]
  refine represents_orthSum_line K one_pos S (Pi.single 0 1) (Y * P) ?_
  rw [transpose_mul, show Pᵀ * Yᵀ * K.gram * (Y * P) = Pᵀ * (Yᵀ * K.gram * Y) * P by
    simp only [Matrix.mul_assoc], hY]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, lowerBlock, Matrix.mul_apply, Fin.sum_univ_two, h1, h01, h02, h10, h20, h21,
      vecMulVec_apply]

/-- In a reduced basis of minimum 1, the first basis vector is orthogonal to the others. -/
theorem unit_orth {S : GramLattice (Fin 3)} (hred : (ternOf S).IsReduced)
    (ha : (ternOf S).a = 1) : (ternOf S).b = 0 ∧ (ternOf S).d = 0 :=
  ⟨by have := hred.b_nonneg; have := hred.two_b_le_a; omega,
    abs_eq_zero.mp (by have := hred.two_d_le; have := abs_nonneg (ternOf S).d; omega)⟩

/-- `⟨1, 1, 2⟩ ⊥ A₂ ⊥ ⟨1⟩ ⊆ L₆`: a unit vector of `I₃` and its complement. -/
theorem L6_represents_unit : L6.Represents (kko112.orthSum (line 1 one_pos)) := by
  refine ⟨Matrix.of fun p q => ?_, ?_⟩
  · exact match p, q with
      | .inl (.inl 0), .inr _ => 1
      | .inl (.inl 1), .inl (.inl 0) => 1
      | .inl (.inl 2), .inl (.inl 1) => 1
      | .inl (.inr _), .inl (.inl 2) => 1
      | .inr a, .inl (.inr b) => if a = b then 1 else 0
      | _, _ => 0
  · decide +kernel

/-- `⟨1, 1, 3⟩ ⊥ A₂ ⊥ ⟨1⟩ ⊆ L₉`: a unit vector of `I₃` and its complement. -/
theorem L9_represents_unit : L9.Represents (kko113.orthSum (line 1 one_pos)) := by
  refine ⟨Matrix.of fun p q => ?_, ?_⟩
  · exact match p, q with
      | .inl (.inl 0), .inl (.inl 0) => 1
      | .inl (.inl 1), .inl (.inl 1) => 1
      | .inr _, .inl (.inl 2) => 1
      | .inl (.inr a), .inl (.inr b) => if a = b then 1 else 0
      | .inl (.inl 2), .inr _ => 1
      | _, _ => 0
  · decide +kernel

/-- **The minimum-1 case for `L₆`** (§2). In a reduced basis `S = ⟨1⟩ ⊥ S′`, and
`⟨1, 1, 2⟩ ⊥ A₂`, which is 2-universal (`kko112_universal`), represents `S′`. -/
theorem L6_represents_of_unit (S : GramLattice (Fin 3))
    (hred : (ternOf S).IsReduced) (ha : (ternOf S).a = 1) : L6.Represents S :=
  have h := unit_orth hred ha
  L6_represents_unit.trans (represents_of_unit kko112 S ha h.1 h.2 (kko112_universal le_rfl _))

/-- **The minimum-1 case for `L₉`** (§2). In a reduced basis `S = ⟨1⟩ ⊥ S′`, and
`⟨1, 1, 3⟩ ⊥ A₂`, which is 2-universal (`kko113_universal`), represents `S′`. -/
theorem L9_represents_of_unit (S : GramLattice (Fin 3))
    (hred : (ternOf S).IsReduced) (ha : (ternOf S).a = 1) : L9.Represents S :=
  have h := unit_orth hred ha
  L9_represents_unit.trans (represents_of_unit kko113 S ha h.1 h.2 (kko113_universal le_rfl _))

end Unit

/-! ### Theorem 1.2 -/

/-- **The skeleton of §2.** If `L` represents every maximal reduced ternary of minimum 1
(`unit`) and every maximal reduced ternary of minimum at least 2 (`minTwo`), then `L` is
3-universal. -/
theorem isUniversal_three_of_steps {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (unit : ∀ S : GramLattice (Fin 3), (ternOf S).IsReduced → (ternOf S).a = 1 →
      L.Represents S)
    (minTwo : ∀ S : GramLattice (Fin 3), IsMaximal S.gram → (ternOf S).IsReduced →
      2 ≤ (ternOf S).a → L.Represents S) :
    L.IsUniversal 3 := by
  refine isUniversal_of_rank _ 3 fun S => ?_
  obtain ⟨S', hmax, hred, hS'⟩ := exists_maximal_reduced S
  refine Represents.trans ?_ hS'
  by_cases ha : (ternOf S').a = 1
  · exact unit S' hred ha
  · exact minTwo S' hmax hred (by have := a_pos S'; omega)

/-- §4 for `L₆`: every maximal reduced ternary of minimum at least 2. -/
def MinTwo6 : Prop :=
  ∀ S : GramLattice (Fin 3), IsMaximal S.gram → (ternOf S).IsReduced →
    2 ≤ (ternOf S).a → L6.Represents S

/-- §4 for `L₉`: every maximal reduced ternary of minimum at least 2. -/
def MinTwo9 : Prop :=
  ∀ S : GramLattice (Fin 3), IsMaximal S.gram → (ternOf S).IsReduced →
    2 ≤ (ternOf S).a → L9.Represents S

/-- **Theorem 1.2(i)**, from §4. -/
theorem L6_isUniversal (h6 : MinTwo6) : L6.IsUniversal 3 :=
  isUniversal_three_of_steps L6 L6_represents_of_unit h6

/-- **Theorem 1.2(ii)**, from §4. -/
theorem L9_isUniversal (h9 : MinTwo9) : L9.IsUniversal 3 :=
  isUniversal_three_of_steps L9 L9_represents_of_unit h9

/-- **Theorem 1.2**, from §4. -/
theorem mainTheorem_of_minTwo (h6 : MinTwo6) (h9 : MinTwo9) : MainTheorem :=
  ⟨L6_isUniversal h6, L9_isUniversal h9, not_isUniversal_I6A2⟩

end KimKimOh

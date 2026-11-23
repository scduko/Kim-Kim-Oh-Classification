import KimKimOh.Bridge.Transfer
import KimKimOh.Genus.K3K9

/-!
# `lem:functional`, global part

A positive lattice represented by `K₃` (or `K₉`) modulo every prime power is represented by it
(`localGlobal_K3`, `localGlobal_K9`; §4 uses them for ternaries). From Hanke's genus representation
theorem and class number 1 of `K₃`, `K₉` (`Genera.rep_g3`, `Genera.rep_g9`), through the transfer
lemmas of `Bridge.Transfer`.
-/

namespace KimKimOh

open GramLattice

/-- **`lem:functional` for `K₃ = I₃ ⊥ A₂`**, the local–global principle, for sources of every rank: a positive
lattice represented by `K₃` over every `ℤ_p` is represented by `K₃`. -/
theorem localGlobal_K3 {v : ℕ} (S : GramLattice (Fin v))
    (h : ∀ p : ℕ, p.Prime → LocallyRepresents K3.gram S.gram p) : K3.Represents S :=
  represents_of_rep K3 relabelK3 _ g3_eq_K3 S (Genera.rep_g3 (posDef_ofMatrixZ S)
    fun p _ => repOver_of_locallyRepresents K3 relabelK3 _ g3_eq_K3 S p (h p Fact.out))

/-- **`lem:functional` for `K₉ = I₂ ⊥ A₂ ⊥ ⟨3⟩`**, for sources of every rank. -/
theorem localGlobal_K9 {v : ℕ} (S : GramLattice (Fin v))
    (h : ∀ p : ℕ, p.Prime → LocallyRepresents K9.gram S.gram p) : K9.Represents S :=
  represents_of_rep K9 relabelK9 _ g9_eq_K9 S (Genera.rep_g9 (posDef_ofMatrixZ S)
    fun p _ => repOver_of_locallyRepresents K9 relabelK9 _ g9_eq_K9 S p (h p Fact.out))

end KimKimOh

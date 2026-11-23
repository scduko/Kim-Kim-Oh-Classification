import KimKimOh.Lattices

/-!
# Statement of the main theorem

Theorem 1.2 of the paper:

1. `I₃ ⊥ A₁ ⊥ A₂` is 3-universal;
2. `I₃ ⊥ A₂ ⊥ ⟨3⟩` is 3-universal;
3. `I₆ ⊥ A₂` is not 5-universal.

These are the three starred cases of the Kim–Kim–Oh list. `MainTheorem` is recorded as a
proposition:

- `mainTheorem` (`KimKimOh/Main.lean`) proves it, without hypotheses;
- part 3 has a short proof of its own (`not_isUniversal_I6A2`, `KimKimOh/Quinary.lean`).

The paper's count of exactly eleven 3-universal lattices of rank 6 and two 5-universal
lattices of rank 8 additionally uses the earlier Kim–Kim–Oh candidate list. That count is
not stated here.
-/

namespace KimKimOh

open GramLattice

/-- Theorem 1.2 of the paper. -/
def MainTheorem : Prop :=
  L6.IsUniversal 3 ∧ L9.IsUniversal 3 ∧ ¬ I6A2.IsUniversal 5

end KimKimOh

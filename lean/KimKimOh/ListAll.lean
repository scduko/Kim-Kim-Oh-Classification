import Mathlib.Data.List.Basic

/-!
# Conjunctions over a list

`allP P l` is `P x₁ ∧ P x₂ ∧ … ∧ True` for `l = [x₁, x₂, …]`. A generated assembly proves it by a
chain of `And.intro` from per-entry kernel checks, and `allP_mem` turns it into `∀ x ∈ l, P x`
without `simp`.
-/

namespace KimKimOh

/-- `P x` for every entry `x` of `l`, as a conjunction. -/
def allP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: l => P x ∧ allP P l

theorem allP_mem {α : Type} {P : α → Prop} : ∀ {l : List α}, allP P l → ∀ x ∈ l, P x
  | [], _, x, hx => by simp at hx
  | y :: l, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact allP_mem h.2 x hx

end KimKimOh

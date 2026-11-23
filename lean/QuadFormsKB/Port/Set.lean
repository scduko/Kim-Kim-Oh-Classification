-- Added for the Lean 4.36 port in this repository; see QuadFormsKB/PORT.md.
import Mathlib.Data.Set.Card

/-!
# Subtypes and sets after the Mathlib v4.36 change to `Set`

`{x // p x}` is no longer syntactically `↥{x | p x}`, so `Nat.card_coe_set_eq _` no longer
unifies with `Nat.card {x // p x} = {x | p x}.ncard`; this states that form.
-/

namespace QuadFormsKB.Port

theorem natCard_subtype_eq_ncard {α : Type*} (p : α → Prop) :
    Nat.card {x // p x} = {x | p x}.ncard :=
  Nat.card_coe_set_eq {x | p x}

end QuadFormsKB.Port

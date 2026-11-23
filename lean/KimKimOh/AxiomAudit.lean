import Lean

/-!
# The axiom audit command

`#assert_standard_axioms c` fails unless the constant `c` depends only on `propext`,
`Classical.choice` and `Quot.sound`, and otherwise logs its axioms. The audits
`scripts/CheckAxioms.lean` (the light theorems) and `scripts/CheckAxiomsMain.lean` (the main
theorem, after the kernel checks of §4) use it.
-/

open Lean Elab Command in
/-- Fail unless the given constant depends only on `propext`, `Classical.choice` and
`Quot.sound`. -/
elab "#assert_standard_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms name
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let bad := axioms.filter (!standard.contains ·)
  if bad.isEmpty then
    logInfo m!"{name}: {axioms.toList}"
  else
    throwError m!"{name} depends on non-standard axioms {bad.toList}"

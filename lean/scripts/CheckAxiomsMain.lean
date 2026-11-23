import KimKimOh.AxiomAudit
import KimKimOh.Main

/-!
# Axiom check for the headline theorem

Run locally after a full build: `lake env lean scripts/CheckAxiomsMain.lean`. It needs the kernel
checks of §4 (`FirstPassChecks`, `Terminal`), several CPU-hours, so CI does not run it.
-/

#assert_standard_axioms KimKimOh.mainTheorem
#assert_standard_axioms KimKimOh.kko112_universal
#assert_standard_axioms KimKimOh.kko113_universal
#assert_standard_axioms KimKimOh.minTwo6
#assert_standard_axioms KimKimOh.minTwo9
#assert_standard_axioms KimKimOh.mainTheorem_of_minTwo
#assert_standard_axioms KimKimOh.minTwo_of_checks
#assert_standard_axioms KimKimOh.termOK_sound
#assert_standard_axioms KimKimOh.exists_normal
#assert_standard_axioms KimKimOh.region_cover
#assert_standard_axioms KimKimOh.blockOK_sound
#assert_standard_axioms KimKimOh.termAll3
#assert_standard_axioms KimKimOh.termAll9
#assert_standard_axioms KimKimOh.enum3_all
#assert_standard_axioms KimKimOh.enum9_all

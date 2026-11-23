import KimKimOh.AxiomAudit
import KimKimOh.MinTwoOfChecks
import KimKimOh.Assembly
import KimKimOh.Local.LargePrimes
import KimKimOh.Quinary
import KimKimOh.Tables.Soundness
import KimKimOh.Bridge.LocalGlobal
import KimKimOh.Genus.Kko112
import KimKimOh.Genus.Kko113

/-!
# Axiom check without the kernel checks of §4

Run by CI: `lake env lean scripts/CheckAxioms.lean`. It fails unless every listed theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`. The full check, which needs
the kernel checks of §4, is `scripts/CheckAxiomsMain.lean`.
-/

#assert_standard_axioms KimKimOh.mainTheorem_of_minTwo
#assert_standard_axioms KimKimOh.minTwo_of_checks
#assert_standard_axioms KimKimOh.region_cover
#assert_standard_axioms KimKimOh.blockOK_sound
#assert_standard_axioms KimKimOh.enumOK_sound
#assert_standard_axioms KimKimOh.rep_of_optCover
#assert_standard_axioms KimKimOh.termOK_sound
#assert_standard_axioms KimKimOh.exists_normal
#assert_standard_axioms KimKimOh.termAll_of_batches
#assert_standard_axioms KimKimOh.L6_isUniversal
#assert_standard_axioms KimKimOh.L9_isUniversal
#assert_standard_axioms KimKimOh.L6_represents_of_unit
#assert_standard_axioms KimKimOh.L9_represents_of_unit
#assert_standard_axioms KimKimOh.not_isUniversal_I6A2
#assert_standard_axioms KimKimOh.rank_K3
#assert_standard_axioms KimKimOh.rank_K9
#assert_standard_axioms KimKimOh.square_K3
#assert_standard_axioms KimKimOh.square_K9
#assert_standard_axioms KimKimOh.Local.Precision.locallyRepresents_of_precision_two
#assert_standard_axioms KimKimOh.Local.Precision.locallyRepresents_of_precision_three
#assert_standard_axioms KimKimOh.scalar_slice
#assert_standard_axioms KimKimOh.scalar_slice_one
#assert_standard_axioms KimKimOh.not_four_dvd_det_of_isMaximal
#assert_standard_axioms KimKimOh.Local.locallyRepresents_K3_two
#assert_standard_axioms KimKimOh.Local.locallyRepresents_K9_two
#assert_standard_axioms KimKimOh.Local.locallyRepresents_K3_three
#assert_standard_axioms KimKimOh.Local.locallyRepresents_K9_three
#assert_standard_axioms KimKimOh.Windows.ap_sieve
#assert_standard_axioms KimKimOh.Windows.ie_bound
#assert_standard_axioms KimKimOh.Windows.window_survivor'
#assert_standard_axioms KimKimOh.Primes.card_le_of_lt_P
#assert_standard_axioms KimKimOh.atMostClasses_one_not_okAt
#assert_standard_axioms KimKimOh.represents_of_scalarCost
#assert_standard_axioms KimKimOh.Windows.tail_ineq
#assert_standard_axioms KimKimOh.Tables.local2_K3
#assert_standard_axioms KimKimOh.Tables.local2_K9
#assert_standard_axioms KimKimOh.Tables.local3_K3
#assert_standard_axioms KimKimOh.Tables.local3_K9
#assert_standard_axioms KimKimOh.localGlobal_K3
#assert_standard_axioms KimKimOh.localGlobal_K9
#assert_standard_axioms KimKimOh.kko112_universal
#assert_standard_axioms KimKimOh.kko113_universal

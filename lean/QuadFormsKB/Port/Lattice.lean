-- Added for the Lean 4.36 port in this repository; see QuadFormsKB/PORT.md.
import Mathlib.Algebra.Module.Lattice.Full

/-!
# Building a full lattice from `FG` and spanning

Mathlib v4.36 split the old `Submodule.IsLattice` (`fg`, `span_eq_top`) into `IsLattice` and
`IsFullLattice`; the anonymous constructor `⟨fg, span⟩` no longer applies. Over a fraction ring,
finite generation gives `IsLattice`, and spanning makes it full.
-/

namespace QuadFormsKB.Port

theorem isFullLattice_of_fg_span {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    {M : Submodule R V} (hfg : M.FG) (hspan : Submodule.span K (M : Set V) = ⊤) :
    M.IsFullLattice K :=
  haveI := Submodule.IsLattice.of_fg K hfg
  ⟨hspan⟩

end QuadFormsKB.Port

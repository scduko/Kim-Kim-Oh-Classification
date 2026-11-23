-- Added for the Lean 4.36 port in this repository; see QuadFormsKB/PORT.md.
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# The real embedding of the completion at a real place, on the number field

Mathlib v4.36 no longer simplifies `extensionEmbeddingOfIsReal hw (algebraMap F w.Completion x)`
to `embedding_of_isReal hw x`; this restores the simplification.
-/

open NumberField

namespace QuadFormsKB.Port

@[simp]
theorem extensionEmbeddingOfIsReal_algebraMap {F : Type*} [Field F] {w : InfinitePlace F}
    (hw : w.IsReal) (a : F) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap F w.Completion a) =
      InfinitePlace.embedding_of_isReal hw a := by
  rw [AbsoluteValue.Completion.algebraMap_def, InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  rfl

end QuadFormsKB.Port

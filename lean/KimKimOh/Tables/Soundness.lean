import KimKimOh.Tables.Check32
import KimKimOh.Tables.Check92
import KimKimOh.Tables.Check33
import KimKimOh.Tables.Check93

/-!
# The local tests at 2 and 3 (`app:correction-tests`)

A ternary whose Gram residue is accepted by the certified table of `K₃` (or `K₉`) at 2 or 3 is
represented by `K₃` (or `K₉`) over `ℤ₂` or `ℤ₃`: `sound2` and `sound3` with
`lem:local-precision` for the diagonal sublattices of `KimKimOh/Local/Diagonal.lean`.
-/

namespace KimKimOh.Tables

open Matrix KimKimOh.Local

theorem J32_eq : J32 = diagonal (fun r : Fin 5 => (J32f r : ℤ)) := by
  unfold J32; congr 1; funext r; fin_cases r <;> rfl
theorem J92_eq : J92 = diagonal (fun r : Fin 5 => (J92f r : ℤ)) := by
  unfold J92; congr 1; funext r; fin_cases r <;> rfl
theorem J33_eq : J33 = diagonal (fun r : Fin 5 => (J33f r : ℤ)) := by
  unfold J33; congr 1; funext r; fin_cases r <;> rfl
theorem J93_eq : J93 = diagonal (fun r : Fin 5 => (J93f r : ℤ)) := by
  unfold J93; congr 1; funext r; fin_cases r <;> rfl

/-- **The local test of `K₃` at 2.** -/
theorem local2_K3 (g : Tern) (h : accepted2 acc32 g = true) :
    LocallyRepresents K3.gram g.toMatrix 2 :=
  sound2 K3.gram J32f (fun X Y hY C hC h4 h8 => locallyRepresents_K3_two X Y hY C hC
    (by rw [J32_eq]; exact h4) (by rw [J32_eq]; exact h8)) acc32 wit32 accOK32 g h

/-- **The local test of `K₉` at 2.** -/
theorem local2_K9 (g : Tern) (h : accepted2 acc92 g = true) :
    LocallyRepresents K9.gram g.toMatrix 2 :=
  sound2 K9.gram J92f (fun X Y hY C hC h4 h8 => locallyRepresents_K9_two X Y hY C hC
    (by rw [J92_eq]; exact h4) (by rw [J92_eq]; exact h8)) acc92 wit92 accOK92 g h

/-- **The local test of `K₃` at 3.** -/
theorem local3_K3 (g : Tern) (h : accepted3 acc33 g = true) :
    LocallyRepresents K3.gram g.toMatrix 3 :=
  sound3 K3.gram J33f (fun X Y hY C hC h9 => locallyRepresents_K3_three X Y hY C hC
    (by rw [J33_eq]; exact h9)) acc33 wit33 accOK33 g h

/-- **The local test of `K₉` at 3.** -/
theorem local3_K9 (g : Tern) (h : accepted3 acc93 g = true) :
    LocallyRepresents K9.gram g.toMatrix 3 :=
  sound3 K9.gram J93f (fun X Y hY C hC h9 => locallyRepresents_K9_three X Y hY C hC
    (by rw [J93_eq]; exact h9)) acc93 wit93 accOK93 g h

end KimKimOh.Tables

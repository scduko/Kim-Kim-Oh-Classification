import KimKimOh.Bridge.LocalGlobal
import KimKimOh.Local.Binary
import KimKimOh.Hosts

/-!
# Kim–Kim–Oh, Theorem 1, for `⟨1, 1, 3⟩ ⊥ A₂`

`kko113 = ⟨1, 1, 3⟩ ⊥ A₂` is `K₉ = I₂ ⊥ A₂ ⊥ ⟨3⟩` in another order of its basis. `K₉` has class
number 1, so it represents every positive lattice that it represents over every `ℤ_p`
(`localGlobal_K9`), and it represents every binary form of positive determinant over every
`ℤ_p` (`LocalBinary.locallyRepresents_K9_binary`). Hence `K₉`, and `kko113`, are 2-universal.
-/

namespace KimKimOh

open Matrix GramLattice Local

/-- **`K₉` is 2-universal.** -/
theorem K9_isUniversal_two : K9.IsUniversal 2 :=
  isUniversal_of_rank K9 2 fun T => localGlobal_K9 T fun p hp =>
    LocalBinary.locallyRepresents_K9_binary T.gram T.gram_isSymm.eq T.gram_det_pos p hp

/-- The basis of `K₉` in the coordinates of `kko113`. -/
def k9In113 : (Fin 2 ⊕ Fin 2) ⊕ Fin 1 → Fin 3 ⊕ Fin 2
  | .inl (.inl i) => .inl (Fin.castLE (by omega) i)
  | .inl (.inr j) => .inr j
  | .inr _ => .inl 2

/-- `kko113` represents `K₉` (they are isometric). -/
theorem kko113_represents_K9 : kko113.Represents K9 :=
  ⟨Matrix.of fun a b => if a = k9In113 b then 1 else 0, by decide +kernel⟩

/-- **Kim–Kim–Oh, Theorem 1: `⟨1, 1, 3⟩ ⊥ A₂` is 2-universal.** -/
theorem kko113_universal : kko113.IsUniversal 2 :=
  fun _ hm T => kko113_represents_K9.trans (K9_isUniversal_two hm T)

end KimKimOh

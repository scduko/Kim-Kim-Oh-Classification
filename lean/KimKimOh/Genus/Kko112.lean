import KimKimOh.Genus.Kko112Hard
import KimKimOh.Genus.Kko112FromK6

/-!
# Kim–Kim–Oh, Theorem 1, for `⟨1, 1, 2⟩ ⊥ A₂`

`kko112_universal`: `kko112 = K₂₂ = ⟨1, 1, 2⟩ ⊥ A₂` is 2-universal. Kim–Kim–Oh, §4:

* `K₂₂` represents every positive binary `S` over every `ℤ_p` (`locallyRepresents_kko112_binary`),
  so `S` is represented by a form in the genus of `K₂₂`, which is `{K₂₂, K₆}`, `K₆ = I₄ ⊥ ⟨6⟩`
  (`Genera.rep_g22_or_k6`).
* If `K₆` represents `S`, then `K₂₂` represents `S` (Lemma 1, `rep_of_k6`), unless `S` is even with
  odd off-diagonal entry and `det S ≡ 1 (mod 3)`; those binaries are represented by `K₂₂` through
  `N = ⟨1, 1⟩ ⊥ A₂` (`kko112_represents_hard`).
-/

open Matrix

namespace KimKimOh

open GramLattice Genera QuadFormsKB QuadFormsKB.LocalDensity

/-- `Fin 5 ≃ Fin 3 ⊕ Fin 2`: the `A₂` and `⟨2⟩` coordinates of `g22` first. -/
def relabelK22Fun : Fin 5 → Fin 3 ⊕ Fin 2 := ![.inr 0, .inr 1, .inl 2, .inl 0, .inl 1]

/-- The relabelling of `K₂₂`. -/
noncomputable def relabelK22 : Fin 5 ≃ Fin 3 ⊕ Fin 2 := Equiv.ofBijective relabelK22Fun (by decide)

theorem g22_eq_kko112 : g22 = kko112.gram.submatrix relabelK22 relabelK22 := by
  rw [g22_eq]; decide

/-- **`⟨1, 1, 2⟩ ⊥ A₂` represents every positive binary.** -/
theorem kko112_represents_binary (S : GramLattice (Fin 2)) : kko112.Represents S := by
  have hloc : ∀ (p : ℕ) [Fact p.Prime], Watson1963.RepOver ℤ_[p] (ofMatrixZ g22) (ofMatrixZ S.gram) :=
    fun p _ => repOver_of_locallyRepresents kko112 relabelK22 g22 g22_eq_kko112 S p
      (Kko112.locallyRepresents_kko112_binary S.gram S.gram_isSymm.eq S.gram_det_pos p Fact.out)
  rcases rep_g22_or_k6 (posDef_ofMatrixZ S) hloc with h | h
  · exact represents_of_rep kko112 relabelK22 g22 g22_eq_kko112 S h
  · obtain ⟨X, hX⟩ := matrix_of_rep k6_symm.eq S h
    rcases Kko112.rep_of_k6 X with ⟨Y, hY⟩ | ⟨h00, h11, h01, h3⟩
    · exact represents_of_rep kko112 relabelK22 g22 g22_eq_kko112 S (rep_of_matrix Y (hY.trans hX))
    · rw [hX] at h00 h11 h01 h3
      refine Kko112.kko112_represents_hard S ?_ ?_ ?_ ?_
      · exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h00)
      · exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h11)
      · have := (ZMod.intCast_eq_intCast_iff' (S.gram 0 1) 1 2).mp (by simpa using h01)
        simpa using this
      · have := (ZMod.intCast_eq_intCast_iff' S.gram.det 1 3).mp (by simpa using h3)
        simpa using this

/-- **Kim–Kim–Oh, Theorem 1: `⟨1, 1, 2⟩ ⊥ A₂` is 2-universal.** -/
theorem kko112_universal : kko112.IsUniversal 2 :=
  isUniversal_of_rank kko112 2 kko112_represents_binary

end KimKimOh

import KimKimOh.TermLifts

/-!
# Normalizing the signs of the last column (`app:bounded`)

The enumeration of last columns assumes `d ≥ 0`, `e ≥ 0` if `d = 0`, and `a e ≥ b d` if `b = 0`
or `2 b = a` (`Tern.Normal`). A reduced maximal ternary has an isometric one with the same leading
block, reduced, maximal and normalized (`exists_normal`): negate `e₃`; then, if `b = 0`, negate
`e₂`, or, if `2 b = a`, replace `e₂` by `e₁ - e₂`.
-/

namespace KimKimOh

open GramLattice Matrix

/-- `e₃ ↦ -e₃`. -/
def Tern.negE3 (g : Tern) : Tern := ⟨g.a, g.b, g.c, -g.d, -g.e, g.f⟩

/-- `e₂ ↦ -e₂`. -/
def Tern.negE2 (g : Tern) : Tern := ⟨g.a, -g.b, g.c, g.d, -g.e, g.f⟩

/-- `e₂ ↦ e₁ - e₂`. -/
def Tern.shear (g : Tern) : Tern := ⟨g.a, g.a - g.b, g.a - 2 * g.b + g.c, g.d, g.d - g.e, g.f⟩

theorem Tern.negE3_reduced {g : Tern} (h : g.IsReduced) : g.negE3.IsReduced where
  b_nonneg := h.b_nonneg
  two_b_le_a := h.two_b_le_a
  a_le_c := h.a_le_c
  two_d_le := by simpa [Tern.negE3] using h.two_d_le
  two_mu_le := by
    have := h.two_mu_le
    simp only [Tern.negE3, Tern.delta] at this ⊢
    rw [show g.a * -g.e - g.b * -g.d = -(g.a * g.e - g.b * g.d) by ring, abs_neg]; exact this
  a_le_f := h.a_le_f
  delta_le_proj := by simpa [Tern.negE3, Tern.delta] using h.delta_le_proj
  height := by
    have := h.height
    simp only [Tern.negE3, Tern.det, Tern.delta] at this ⊢; linarith
  a_le_eval := fun x y z hne => by
    have := h.a_le_eval x y (-z) (by intro h'; apply hne; simp_all)
    simp only [Tern.negE3, Tern.eval] at this ⊢; linarith

theorem Tern.negE2_reduced {g : Tern} (h : g.IsReduced) (hb : g.b = 0) : g.negE2.IsReduced where
  b_nonneg := by simp [Tern.negE2, hb]
  two_b_le_a := by have := h.two_b_le_a; simp [Tern.negE2, hb] at this ⊢; linarith
  a_le_c := h.a_le_c
  two_d_le := h.two_d_le
  two_mu_le := by
    have := h.two_mu_le
    simp only [Tern.negE2, Tern.delta, hb] at this ⊢
    rw [show g.a * -g.e - -0 * g.d = -(g.a * g.e - 0 * g.d) by ring, abs_neg]; simpa using this
  a_le_f := h.a_le_f
  delta_le_proj := by simpa [Tern.negE2, Tern.delta] using h.delta_le_proj
  height := by
    have := h.height
    simp only [Tern.negE2, Tern.det, Tern.delta] at this ⊢; linarith
  a_le_eval := fun x y z hne => by
    have := h.a_le_eval x (-y) z (by intro h'; apply hne; simp_all)
    simp only [Tern.negE2, Tern.eval] at this ⊢; linarith

theorem Tern.shear_reduced {g : Tern} (h : g.IsReduced) (hb : 2 * g.b = g.a) :
    g.shear.IsReduced where
  b_nonneg := by have := h.two_b_le_a; have := h.b_nonneg; simp only [Tern.shear]; linarith
  two_b_le_a := by have := h.b_nonneg; simp only [Tern.shear]; linarith
  a_le_c := by have := h.a_le_c; simp only [Tern.shear]; linarith
  two_d_le := h.two_d_le
  two_mu_le := by
    have := h.two_mu_le
    simp only [Tern.shear, Tern.delta] at this ⊢
    rw [show g.a * (g.d - g.e) - (g.a - g.b) * g.d = -(g.a * g.e - g.b * g.d) by ring, abs_neg,
      show g.a * (g.a - 2 * g.b + g.c) - (g.a - g.b) * (g.a - g.b) = g.a * g.c - g.b * g.b by ring]
    exact this
  a_le_f := h.a_le_f
  delta_le_proj := by
    have := h.delta_le_proj
    simp only [Tern.shear, Tern.delta] at this ⊢
    linarith
  height := by
    have := h.height
    have e1 : g.shear.delta = g.delta := by simp only [Tern.shear, Tern.delta]; ring
    have e2 : g.shear.det = g.det := by simp only [Tern.shear, Tern.det, Tern.delta]; ring
    rw [e1, e2]; exact this
  a_le_eval := fun x y z hne => by
    have := h.a_le_eval (x + y) (-y) z (by
      intro h'; apply hne; simp only [Prod.mk.injEq] at h' ⊢; omega)
    simp only [Tern.shear, Tern.eval] at this ⊢; linarith

/-! ### The transforms as changes of basis -/

theorem isUnit_det_of_eq {W : Matrix (Fin 3) (Fin 3) ℤ} {u : ℤ} (h : W.det = u) (hu : u = 1 ∨ u = -1) :
    IsUnit W.det := by
  rw [h]; rcases hu with rfl | rfl
  · exact isUnit_one
  · exact isUnit_one.neg

theorem conj_negE3 (S : GramLattice (Fin 3)) :
    ∃ (W : Matrix (Fin 3) (Fin 3) ℤ) (hW : IsUnit W.det),
      ternOf (S.conj W hW) = (ternOf S).negE3 := by
  refine ⟨!![1, 0, 0; 0, 1, 0; 0, 0, -1],
    isUnit_det_of_eq (u := -1) (by simp [Matrix.det_fin_three]) (Or.inr rfl), ?_⟩
  have h10 := S.gram_comm 1 0; have h20 := S.gram_comm 2 0; have h21 := S.gram_comm 2 1
  ext <;> simp [Tern.ofMatrix, Tern.negE3, conj_gram, Matrix.mul_apply, Fin.sum_univ_three]

theorem conj_negE2 (S : GramLattice (Fin 3)) :
    ∃ (W : Matrix (Fin 3) (Fin 3) ℤ) (hW : IsUnit W.det),
      ternOf (S.conj W hW) = (ternOf S).negE2 := by
  refine ⟨!![1, 0, 0; 0, -1, 0; 0, 0, 1],
    isUnit_det_of_eq (u := -1) (by simp [Matrix.det_fin_three]) (Or.inr rfl), ?_⟩
  have h10 := S.gram_comm 1 0; have h20 := S.gram_comm 2 0; have h21 := S.gram_comm 2 1
  ext <;> simp [Tern.ofMatrix, Tern.negE2, conj_gram, Matrix.mul_apply, Fin.sum_univ_three]

theorem conj_shear (S : GramLattice (Fin 3)) :
    ∃ (W : Matrix (Fin 3) (Fin 3) ℤ) (hW : IsUnit W.det),
      ternOf (S.conj W hW) = (ternOf S).shear := by
  refine ⟨!![1, 1, 0; 0, -1, 0; 0, 0, 1],
    isUnit_det_of_eq (u := -1) (by simp [Matrix.det_fin_three]) (Or.inr rfl), ?_⟩
  have h10 := S.gram_comm 1 0; have h20 := S.gram_comm 2 0; have h21 := S.gram_comm 2 1
  ext <;> simp [Tern.ofMatrix, Tern.shear, conj_gram, Matrix.mul_apply, Fin.sum_univ_three, h10,
    h20, h21] <;> ring

/-- A transform realized by a change of basis keeps maximality, and represents `S`. -/
theorem transform_lattice (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) {T : Tern → Tern}
    (hT : ∃ (W : Matrix (Fin 3) (Fin 3) ℤ) (hW : IsUnit W.det), ternOf (S.conj W hW) = T (ternOf S)) :
    ∃ S' : GramLattice (Fin 3), IsMaximal S'.gram ∧ ternOf S' = T (ternOf S) ∧ S'.Represents S := by
  obtain ⟨W, hW, h⟩ := hT
  exact ⟨S.conj W hW, isMaximal_conj hmax W hW, h, conj_represents S W hW⟩

/-- **Normalized signs.** A reduced maximal ternary has an isometric one with the same leading
block, reduced, maximal and with normalized signs. -/
theorem exists_normal (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram)
    (hred : (ternOf S).IsReduced) :
    ∃ S' : GramLattice (Fin 3), IsMaximal S'.gram ∧ (ternOf S').IsReduced ∧ (ternOf S').Normal ∧
      (ternOf S').a = (ternOf S).a ∧ (ternOf S').b = (ternOf S).b ∧
      (ternOf S').c = (ternOf S).c ∧ S'.Represents S := by
  -- the signs of `d` and `e`
  obtain ⟨S₁, hmax₁, hred₁, hd₁, he₁, ha₁, hb₁, hc₁, hrep₁⟩ : ∃ S₁ : GramLattice (Fin 3),
      IsMaximal S₁.gram ∧ (ternOf S₁).IsReduced ∧ 0 ≤ (ternOf S₁).d ∧
      ((ternOf S₁).d = 0 → 0 ≤ (ternOf S₁).e) ∧ (ternOf S₁).a = (ternOf S).a ∧
      (ternOf S₁).b = (ternOf S).b ∧ (ternOf S₁).c = (ternOf S).c ∧ S₁.Represents S := by
    by_cases hneg : (ternOf S).d < 0 ∨ ((ternOf S).d = 0 ∧ (ternOf S).e < 0)
    · obtain ⟨S₁, hm, ht, hr⟩ := transform_lattice S hmax (conj_negE3 S)
      refine ⟨S₁, hm, ht ▸ Tern.negE3_reduced hred, ?_, ?_, ?_, ?_, ?_, hr⟩ <;>
        rw [ht] <;> simp only [Tern.negE3] <;> omega
    · push Not at hneg
      exact ⟨S, hmax, hred, by omega, fun h0 => hneg.2 h0, rfl, rfl, rfl, Represents.refl S⟩
  -- the case `b = 0` or `2 b = a` with `a e < b d`
  by_cases hviol : ((ternOf S₁).b = 0 ∨ 2 * (ternOf S₁).b = (ternOf S₁).a) ∧
      (ternOf S₁).a * (ternOf S₁).e < (ternOf S₁).b * (ternOf S₁).d
  · obtain ⟨hcase, hlt⟩ := hviol
    have ha0 := a_pos S₁
    by_cases hb0 : (ternOf S₁).b = 0
    · obtain ⟨S₂, hm, ht, hr⟩ := transform_lattice S₁ hmax₁ (conj_negE2 S₁)
      refine ⟨S₂, hm, ht ▸ Tern.negE2_reduced hred₁ hb0, ?_, ?_, ?_, ?_, hr.trans hrep₁⟩
      · rw [ht]
        refine ⟨by simpa [Tern.negE2] using hd₁, fun _ => ?_, fun _ => ?_⟩ <;>
          simp only [Tern.negE2] <;> rw [hb0] at hlt <;> nlinarith
      · rw [ht, ← ha₁]; rfl
      · rw [ht, ← hb₁]; simp [Tern.negE2, hb0]
      · rw [ht, ← hc₁]; rfl
    · have h2b : 2 * (ternOf S₁).b = (ternOf S₁).a := by tauto
      obtain ⟨S₂, hm, ht, hr⟩ := transform_lattice S₁ hmax₁ (conj_shear S₁)
      refine ⟨S₂, hm, ht ▸ Tern.shear_reduced hred₁ h2b, ?_, ?_, ?_, ?_, hr.trans hrep₁⟩
      · rw [ht]
        refine ⟨by simpa [Tern.shear] using hd₁, fun hd0 => ?_, fun _ => ?_⟩
        · simp only [Tern.shear] at hd0 ⊢
          rw [hd0] at hlt; nlinarith
        · simp only [Tern.shear]
          nlinarith
      · rw [ht, ← ha₁]; rfl
      · rw [ht, ← hb₁]; simp only [Tern.shear]; linarith
      · rw [ht, ← hc₁]; simp only [Tern.shear]; linarith
  · push Not at hviol
    exact ⟨S₁, hmax₁, hred₁, ⟨hd₁, he₁, fun h' => by have := hviol h'; linarith⟩, ha₁, hb₁, hc₁,
      hrep₁⟩

end KimKimOh

import KimKimOh.Maximal
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Instances.Matrix
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Local representations modulo every `pᵏ` are `p`-adic representations

`LocallyRepresents K S p` (`Maximal.lean`) asks for an integer solution of `Xᵀ K X ≡ S (mod pᵏ)`
for every `k`. `exists_padic_rep` gives a solution over `ℤ_p`: the solutions modulo `pᵏ` form a
decreasing sequence of nonempty closed subsets of the compact space of matrices over `ℤ_p`, and a
point of their intersection solves `Hᵀ K H = S` exactly.
-/

namespace KimKimOh

open Matrix

variable {ι κ : Type*} [Fintype ι]

/-- **A local representation is a `p`-adic representation.** -/
theorem exists_padic_rep (p : ℕ) [Fact p.Prime] (K : Matrix ι ι ℤ) (S : Matrix κ κ ℤ)
    (h : LocallyRepresents K S p) :
    ∃ H : Matrix ι κ ℤ_[p], Hᵀ * K.map (Int.cast : ℤ → ℤ_[p]) * H = S.map (Int.cast : ℤ → ℤ_[p]) := by
  set Kp := K.map (Int.cast : ℤ → ℤ_[p])
  set Sp := S.map (Int.cast : ℤ → ℤ_[p])
  -- the solutions modulo `pᵏ`
  let C : ℕ → Set (Matrix ι κ ℤ_[p]) := fun k =>
    {H | ∀ i j, ‖(Hᵀ * Kp * H - Sp) i j‖ ≤ (p : ℝ) ^ (-(k : ℤ))}
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    have hC : C k = ⋂ i, ⋂ j, {H : Matrix ι κ ℤ_[p] |
        ‖(Hᵀ * Kp * H - Sp) i j‖ ≤ (p : ℝ) ^ (-(k : ℤ))} := by
      ext H
      simp [C]
    rw [hC]
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le ?_ continuous_const
    refine continuous_norm.comp ?_
    have : Continuous fun H : Matrix ι κ ℤ_[p] => Hᵀ * Kp * H - Sp :=
      (((continuous_id.matrix_transpose).matrix_mul continuous_const).matrix_mul
        continuous_id).sub continuous_const
    exact (continuous_apply j).comp ((continuous_apply i).comp this)
  have hmono : ∀ k, C (k + 1) ⊆ C k := by
    intro k H hH i j
    refine (hH i j).trans ?_
    apply zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_le)
    omega
  have hne : ∀ k, (C k).Nonempty := by
    intro k
    obtain ⟨X, hX⟩ := h k
    refine ⟨X.map (Int.cast : ℤ → ℤ_[p]), fun i j => ?_⟩
    have hmap : ((X.map (Int.cast : ℤ → ℤ_[p]))ᵀ * Kp * X.map (Int.cast : ℤ → ℤ_[p]) - Sp) i j =
        (((Xᵀ * K * X) i j - S i j : ℤ) : ℤ_[p]) := by
      simp only [Kp, Sp, Matrix.sub_apply, Matrix.map_apply, Matrix.mul_apply,
        Matrix.transpose_apply]
      push_cast
      rfl
    rw [hmap]
    exact PadicInt.norm_int_le_pow_iff_dvd.mpr (hX i j)
  have : CompactSpace (Matrix ι κ ℤ_[p]) := inferInstanceAs (CompactSpace (ι → κ → ℤ_[p]))
  obtain ⟨H, hH⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hne
    (hclosed 0).isCompact hclosed
  refine ⟨H, ?_⟩
  rw [Set.mem_iInter] at hH
  refine Matrix.ext fun i j => ?_
  rw [← sub_eq_zero, ← Matrix.sub_apply]
  by_contra hne0
  have hpos : 0 < ‖(Hᵀ * Kp * H - Sp) i j‖ := norm_pos_iff.mpr hne0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hp1)
  have := hH k i j
  rw [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
  linarith

end KimKimOh

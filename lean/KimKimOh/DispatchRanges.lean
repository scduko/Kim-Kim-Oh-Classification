import KimKimOh.Enum
import KimKimOh.Compute.Dispatch

/-!
# The dispatcher from its ranges

`dispatchOK_of_ranges`: if the ranges `[w k, w k + w)`, `k < K`, pass `dispatchRange` and
`amaxT t < w K`, then `dispatchOK` holds for `t`.
-/

namespace KimKimOh

open Tables

theorem dispatchOK_of_ranges {j s : ℕ} {prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))}
    {heavy : ℕ → List ℕ} {t w K : ℕ}
    (hK : Nat.blt (amaxT j s prof2 prof3 t) (w * K) = true)
    (h : ∀ k < K, dispatchRange j s prof2 prof3 heavy t (w * k) w = true) :
    dispatchOK j s prof2 prof3 heavy t = true := by
  unfold dispatchOK
  refine natAllR_of_forall fun a ha => ?_
  have hK' := Nat.blt_eq.mp hK
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · rw [h0, zero_mul] at hK'; omega
    · exact h0
  have hk : a / w < K := by
    rw [Nat.div_lt_iff_lt_mul hw]; rw [mul_comm] at hK'; omega
  have := natAllR_spec (h (a / w) hk) (a % w) (Nat.mod_lt _ hw)
  rw [show w * (a / w) + a % w = a from Nat.div_add_mod a w] at this
  have hle : Nat.ble a (amaxT j s prof2 prof3 t) = true := Nat.ble_eq.mpr (by omega)
  rw [hle, Bool.not_true, Bool.false_or] at this
  exact this

end KimKimOh

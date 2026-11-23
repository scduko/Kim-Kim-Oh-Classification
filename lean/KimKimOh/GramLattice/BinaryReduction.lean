import KimKimOh.GramLattice.Isometry
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination

/-!
# Reduced binary lattices

`exists_reduced_binary`: a binary lattice whose minimum is `a`, attained by `v`, has a basis
`v, w` with Gram matrix `[[a, b], [b, c]]`, `0 ≤ 2b ≤ a ≤ c` (Gauss reduction). The vector `v` is
primitive, so it extends to a basis (Bézout); then `w` is moved by a multiple of `v` and its
sign is chosen.
-/

namespace KimKimOh

open Matrix GramLattice

theorem qf_smul {ι : Type*} [Fintype ι] (L : GramLattice ι) (d : ℤ) (v : ι → ℤ) :
    L.qf (d • v) = d ^ 2 * L.qf v := by
  simp only [qf, bf_smul_left, bf_smul_right]
  ring

/-- **Gauss reduction.** A binary lattice of minimum `a`, attained by `v`, has a basis with Gram
matrix `[[a, b], [b, c]]` and `0 ≤ 2b ≤ a ≤ c`. -/
theorem exists_reduced_binary (M : GramLattice (Fin 2)) (v : Fin 2 → ℤ) (hv0 : v ≠ 0) {a : ℤ}
    (hv : M.qf v = a) (hmin : ∀ w, w ≠ 0 → a ≤ M.qf w) :
    ∃ (b c : ℤ) (N : GramLattice (Fin 2)), 0 ≤ 2 * b ∧ 2 * b ≤ a ∧ a ≤ c ∧
      N.gram = !![a, b; b, c] ∧ M.Isometric N := by
  have ha : 0 < a := hv ▸ M.qf_pos hv0
  -- `v` is primitive
  set p := v 0
  set q := v 1
  set g := Int.gcd p q
  have hg : g = 1 := by
    by_contra hg1
    have hg0 : g ≠ 0 := by
      intro h0
      apply hv0
      have := Int.gcd_eq_zero_iff.mp h0
      funext i
      fin_cases i
      · exact this.1
      · exact this.2
    let w : Fin 2 → ℤ := ![p / g, q / g]
    have hw : v = (g : ℤ) • w := by
      funext i
      fin_cases i
      · simp only [w, p, Pi.smul_apply, smul_eq_mul]
        exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))).symm
      · simp only [w, q, Pi.smul_apply, smul_eq_mul]
        exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))).symm
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, smul_zero] at hw
      exact hv0 hw
    have h1 := hmin w hw0
    have h2 : M.qf v = (g : ℤ) ^ 2 * M.qf w := by rw [hw, qf_smul]
    have hg2 : (2 : ℤ) ≤ g := by omega
    have hg4 : (4 : ℤ) ≤ (g : ℤ) ^ 2 := by nlinarith
    have hqw : 0 < M.qf w := M.qf_pos hw0
    nlinarith
  -- Bézout
  set s := Int.gcdA p q
  set t := Int.gcdB p q
  have hbez : p * s + q * t = 1 := by
    have h := Int.gcd_eq_gcd_ab p q
    have hg' : ((Int.gcd p q : ℕ) : ℤ) = 1 := by exact_mod_cast (show Int.gcd p q = 1 from hg)
    linarith
  -- the basis `v, w₀` with `w₀ = (-t, s)`: `det = p s + q t = 1`
  let w₀ : Fin 2 → ℤ := ![-t, s]
  set β := M.bf v w₀
  set k := (2 * β + a) / (2 * a)
  have hk1 : 2 * a * k ≤ 2 * β + a := Int.mul_ediv_self_le (by omega)
  have hk2 : 2 * β + a < 2 * a * (k + 1) := by
    have := Int.lt_mul_ediv_self_add (x := 2 * β + a) (k := 2 * a) (by omega)
    linarith
  set b₀ := β - k * a
  set ε : ℤ := if 0 ≤ b₀ then 1 else -1
  let w : Fin 2 → ℤ := ε • (w₀ - k • v)
  have hbw : M.bf v w = ε * b₀ := by
    simp only [w, bf_smul_right, bf_sub_right, bf_smul_right, qf] at hv ⊢
    rw [hv]
  have hε : ε * b₀ = |b₀| := by
    simp only [ε]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (by omega)]
      ring
  -- the change of basis
  let W : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => if j = 0 then v i else w i
  have hdet : W.det = ε := by
    rw [det_fin_two]
    simp only [W, of_apply, w, w₀, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp
    linear_combination ε * hbez
  have hε1 : ε = 1 ∨ ε = -1 := by simp only [ε]; split_ifs <;> simp
  have hdet' : W.det = 1 ∨ W.det = -1 := hdet ▸ hε1
  have hU : IsUnit W.det := Int.isUnit_iff.mpr hdet'
  let N := M.conj W hU
  have hcol0 : (fun i => W i 0) = v := by funext i; simp [W]
  have hcol1 : (fun i => W i 1) = w := by funext i; simp [W]
  have hw0 : w ≠ 0 := by
    intro h
    have : W.det = 0 := by
      rw [det_fin_two]
      have h0 : ∀ i, W i 1 = 0 := fun i => by simpa [W] using congrFun h i
      rw [h0 0, h0 1]
      ring
    rw [hdet] at this
    rcases hε1 with h1 | h1 <;> rw [h1] at this <;> norm_num at this
  refine ⟨|b₀|, M.qf w, N, by positivity, ?_, hmin w hw0, ?_, isometric_conj M W hU⟩
  · have h1 : -a ≤ 2 * b₀ := by simp only [b₀]; linarith
    have h2 : 2 * b₀ ≤ a := by simp only [b₀]; linarith
    rcases abs_cases b₀ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  · ext i j
    show (Wᵀ * M.gram * W) i j = _
    rw [transpose_mul_mul_apply]
    fin_cases i <;> fin_cases j
    · exact hv
    · simp [hcol0, hcol1, hbw, hε]
    · simp [hcol0, hcol1]
      rw [bf_comm, hbw, hε]
    · simp [hcol1, qf]

end KimKimOh

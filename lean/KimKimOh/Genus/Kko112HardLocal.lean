import KimKimOh.Genus.Kko112HardData
import KimKimOh.Genus.Kko112Local
import KimKimOh.Bridge.LocalGlobal

/-!
# Doubly hard binaries: through `N = ⟨1, 1⟩ ⊥ A₂`

Kim–Kim–Oh treat the binaries `ℓ` that are even unimodular over `ℤ₂` with `d ℓ ≡ 1 (mod 3)`
through `N = ⟨1, 1⟩ ⊥ A₂`, of class number 1, and `K₂₂ = N ⊥ ⟨2⟩`: if `N` represents
`ℓ - 2 v vᵀ`, then `K₂₂` represents `ℓ`. We use `K₃ = N ⊥ ⟨1⟩` instead of the class number of `N`:

* `locallyRepresents_K3_hard`: `K₃` represents `T = ℓ' ⊥ ⟨1⟩` over every `ℤ_p` when `ℓ'` is even
  with odd off-diagonal entry, `d ℓ' ≡ 1 (mod 3)`, and `ℓ' ≢ 0` modulo every prime `p ≥ 5`
  (tables `k3two`, `k3three` at 2 and 3; the rank criterion `rank_K3` at `p ≥ 5`).
* `K₃` has class number 1 (`localGlobal_K3`), so it represents `T`. The vector of norm 1
  of `T` goes to some `±eᵢ`, the only vectors of norm 1 of `K₃`; the rest of `T` lies in
  `eᵢ^⊥ ≅ N`. Adding the vector `v` along `⟨2⟩` gives `kko112_of_K3`.
-/

open Matrix

namespace KimKimOh.Kko112

open Local LocalBinary GramLattice

/-- The `5 × 3` matrix with the entries of a list, row-major. -/
def mat53 (l : List ℤ) : Matrix (Fin 5) (Fin 3) ℤ := Matrix.of fun i j => l.getD (3 * i.val + j.val) 0

/-- `[[a, b], [b, c]] ⊥ ⟨1⟩`. -/
def tern1 (a b c : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![a, b, 0; b, c, 0; 0, 0, 1]

theorem tern1_transpose (a b c : ℤ) : (tern1 a b c)ᵀ = tern1 a b c := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-! ### `p = 2` -/

/-- The test at 2 for `K₃` (through `J32`). -/
def chkK2 (a b c : ℤ) (w : List ℤ × List ℤ) : Bool :=
  decide (∀ i j, (((mat53 w.1)ᵀ * J32 * mat53 w.1) i j - tern1 a b c i j) % 4 = 0) &&
    decide (∀ i, (((mat53 w.1)ᵀ * J32 * mat53 w.1) i i - tern1 a b c i i) % 8 = 0) &&
    decide (∀ i j, (((mat53 w.1)ᵀ * mat53 w.2) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j) % 2 = 0)

theorem k3two_ok : ∀ a : ℕ, a < 8 → ∀ b : ℕ, b < 4 → ∀ c : ℕ, c < 8 →
    (a % 2 == 0 && b % 2 == 1 && c % 2 == 0) = true →
    chkK2 a b c (k3two.getD (32 * a + 8 * b + c) ([], [])) = true := by
  decide +kernel

theorem K3_two (a b c : ℤ) (ha : a % 2 = 0) (hb : b % 2 = 1) (hc : c % 2 = 0) :
    LocallyRepresents K3.gram (tern1 a b c) 2 := by
  obtain ⟨a0, ha0, ha8⟩ := exists_natCast_eq_emod a 8 (by norm_num)
  obtain ⟨b0, hb0, hb4⟩ := exists_natCast_eq_emod b 4 (by norm_num)
  obtain ⟨c0, hc0, hc8⟩ := exists_natCast_eq_emod c 8 (by norm_num)
  have hk := k3two_ok a0 (by omega) b0 (by omega) c0 (by omega) (by simp; omega)
  set w := k3two.getD (32 * a0 + 8 * b0 + c0) ([], [])
  simp only [chkK2, Bool.and_eq_true, decide_eq_true_eq] at hk
  rw [ha0, hb0, hc0] at hk
  obtain ⟨⟨h4', h8'⟩, hY'⟩ := hk
  have hT4 : ∀ i j, (4 : ℤ) ∣ tern1 a b c i j - tern1 (a % 8) (b % 4) (c % 8) i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [tern1] <;> omega
  have hT8 : ∀ i, (8 : ℤ) ∣ tern1 a b c i i - tern1 (a % 8) (b % 4) (c % 8) i i := by
    intro i; fin_cases i <;> simp [tern1] <;> omega
  refine locallyRepresents_K3_two (mat53 w.1) (mat53 w.2) (fun i j => Int.dvd_of_emod_eq_zero (hY' i j))
    (tern1 a b c) (tern1_transpose a b c) (fun i j => ?_) (fun i => ?_)
  · have := dvd_sub (Int.dvd_of_emod_eq_zero (h4' i j)) (hT4 i j)
    simpa only [sub_sub_sub_cancel_right] using this
  · have := dvd_sub (Int.dvd_of_emod_eq_zero (h8' i)) (hT8 i)
    simpa only [sub_sub_sub_cancel_right] using this

/-! ### `p = 3` -/

/-- The test at 3 for `K₃` (through `J33`). -/
def chkK3 (a b c : ℤ) (w : List ℤ × List ℤ) : Bool :=
  decide (∀ i j, (tern1 a b c - (mat53 w.1)ᵀ * J33 * mat53 w.1) i j % 9 = 0) &&
    decide (∀ i j, ((mat53 w.1)ᵀ * mat53 w.2 - (1 : Matrix (Fin 3) (Fin 3) ℤ)) i j % 3 = 0)

theorem k3three_ok : ∀ a : ℕ, a < 9 → ∀ b : ℕ, b < 9 → ∀ c : ℕ, c < 9 → ((a * c + 2 * b * b) % 3 == 1) = true →
    chkK3 a b c (k3three.getD (81 * a + 9 * b + c) ([], [])) = true := by
  decide +kernel

theorem K3_three (a b c : ℤ) (h3 : (a * c - b * b) % 3 = 1) :
    LocallyRepresents K3.gram (tern1 a b c) 3 := by
  obtain ⟨a0, ha0, ha9⟩ := exists_natCast_eq_emod a 9 (by norm_num)
  obtain ⟨b0, hb0, hb9⟩ := exists_natCast_eq_emod b 9 (by norm_num)
  obtain ⟨c0, hc0, hc9⟩ := exists_natCast_eq_emod c 9 (by norm_num)
  have hres : (a0 * c0 + 2 * b0 * b0) % 3 = 1 := by
    have e : ((a0 * c0 + 2 * b0 * b0 : ℕ) : ℤ) % 3 = 1 := by
      push_cast
      rw [ha0, hb0, hc0]
      have ea : a % 9 = a - 9 * (a / 9) := by omega
      have eb : b % 9 = b - 9 * (b / 9) := by omega
      have ec : c % 9 = c - 9 * (c / 9) := by omega
      have key : a % 9 * (c % 9) + 2 * (b % 9) * (b % 9) = (a * c - b * b) + 3 * (b * b - 3 * a * (c / 9) -
          3 * c * (a / 9) + 27 * (a / 9) * (c / 9) - 12 * b * (b / 9) + 54 * (b / 9) * (b / 9)) := by
        rw [ea, eb, ec]; ring
      rw [key, Int.add_mul_emod_self_left, h3]
    omega
  have hk := k3three_ok a0 (by omega) b0 (by omega) c0 (by omega) (by simp; omega)
  set w := k3three.getD (81 * a0 + 9 * b0 + c0) ([], [])
  simp only [chkK3, Bool.and_eq_true, decide_eq_true_eq] at hk
  rw [ha0, hb0, hc0] at hk
  obtain ⟨h9', hY'⟩ := hk
  refine locallyRepresents_K3_three (mat53 w.1) (mat53 w.2) (fun i j => Int.dvd_of_emod_eq_zero (hY' i j))
    (tern1 a b c) (tern1_transpose a b c) fun i j => ?_
  have hT : (9 : ℤ) ∣ (tern1 a b c - tern1 (a % 9) (b % 9) (c % 9)) i j := by
    fin_cases i <;> fin_cases j <;> simp [tern1] <;> omega
  have := dvd_add hT (Int.dvd_of_emod_eq_zero (h9' i j))
  simpa only [Matrix.sub_apply, sub_add_sub_cancel] using this

/-! ### `p ≥ 5` -/

theorem K3_large (a b c : ℤ) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hprim : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) :
    LocallyRepresents K3.gram (tern1 a b c) p := by
  let g : Tern := ⟨a, b, c, 0, 0, 1⟩
  have hg : g.RankGeTwoMod p := by
    intro hr
    apply hprim
    have h1 := hr (a * 1 - 0 * 0) (by simp [Tern.minors, g])
    have h2 := hr (c * 1 - 0 * 0) (by simp [Tern.minors, g])
    have h3 := hr (b * 1 - 0 * 0) (by simp [Tern.minors, g])
    simp only [mul_one, mul_zero, sub_zero] at h1 h2 h3
    exact ⟨h1, h3, h2⟩
  have e : g.toMatrix = tern1 a b c := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [← e]
  exact rank_K3 p hp h5 g hg

/-- **`K₃` represents `ℓ' ⊥ ⟨1⟩` over every `ℤ_p`** for the binaries `ℓ'` above. -/
theorem locallyRepresents_K3_hard (a b c : ℤ) (ha : a % 2 = 0) (hb : b % 2 = 1) (hc : c % 2 = 0)
    (h3 : (a * c - b * b) % 3 = 1) (hprim : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c))
    (p : ℕ) (hp : p.Prime) : LocallyRepresents K3.gram (tern1 a b c) p := by
  rcases prime_cases hp with rfl | rfl | h5
  · exact K3_two a b c ha hb hc
  · exact K3_three a b c h3
  · exact K3_large a b c p hp h5 (hprim p hp h5)

/-! ### `ℓ' ⊥ ⟨1⟩` as a lattice -/

/-- `[[a, b], [b, c]] ⊥ ⟨1⟩` for `a > 0`, `ac - b² > 0`. -/
def ternL (a b c : ℤ) (ha : 0 < a) (hd : 0 < a * c - b * b) : GramLattice (Fin 3) where
  gram := tern1 a b c
  posDef := by
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hd' : (0 : ℝ) < a * c - b * b := by exact_mod_cast hd
    refine posDef_of_ldl (U := !![1, (b : ℝ) / a, 0; 0, 1, 0; 0, 0, 1])
      (V := !![1, -(b : ℝ) / a, 0; 0, 1, 0; 0, 0, 1]) (d := ![(a : ℝ), (a * c - b * b) / a, 1]) ?_ ?_ ?_
    · intro i; fin_cases i
      · simpa using ha'
      · exact div_pos hd' ha'
      · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      ring
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [tern1, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;>
        field_simp
      ring

/-! ### From `K₃` to `K₂₂` -/

/-- `A₂` as a bilinear form. -/
def a2f (u0 u1 v0 v1 : ℤ) : ℤ := 2 * u0 * v0 - u0 * v1 - u1 * v0 + 2 * u1 * v1

theorem K3_entry (X : Matrix (Fin 3 ⊕ Fin 2) (Fin 3) ℤ) (l m : Fin 3) :
    (Xᵀ * K3.gram * X) l m = X (.inl 0) l * X (.inl 0) m + X (.inl 1) l * X (.inl 1) m +
      X (.inl 2) l * X (.inl 2) m + a2f (X (.inr 0) l) (X (.inr 1) l) (X (.inr 0) m) (X (.inr 1) m) := by
  simp only [K3, orthSum, stdLattice, diagLattice, rootA2, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.diagonal_apply, Matrix.zero_apply, a2f]
  simp
  ring

theorem kko112_entry (Y : Matrix (Fin 3 ⊕ Fin 2) (Fin 2) ℤ) (l m : Fin 2) :
    (Yᵀ * kko112.gram * Y) l m = Y (.inl 0) l * Y (.inl 0) m + Y (.inl 1) l * Y (.inl 1) m +
      2 * Y (.inl 2) l * Y (.inl 2) m + a2f (Y (.inr 0) l) (Y (.inr 1) l) (Y (.inr 0) m) (Y (.inr 1) m) := by
  simp only [kko112, orthSum, diagLattice, rootA2, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.diagonal_apply, Matrix.zero_apply, a2f]
  simp
  ring

/-- The two indices of `Fin 3` other than `i`. -/
def oth : Fin 3 → Fin 2 → Fin 3
  | 0 => ![1, 2]
  | 1 => ![0, 2]
  | 2 => ![0, 1]

theorem sum3_split (f : Fin 3 → ℤ) (i : Fin 3) : f 0 + f 1 + f 2 = f i + f (oth i 0) + f (oth i 1) := by
  fin_cases i <;> simp [oth] <;> ring

/-- **From `K₃` to `K₂₂`.** If `K₃` represents `ℓ' ⊥ ⟨1⟩`, then `K₂₂` represents `ℓ' + 2 v vᵀ`. -/
theorem kko112_of_K3 (a b c : ℤ) (ha : 0 < a) (hd : 0 < a * c - b * b) (α β : ℤ)
    (h : K3.Represents (ternL a b c ha hd)) :
    ∃ Y : Matrix (Fin 3 ⊕ Fin 2) (Fin 2) ℤ,
      Yᵀ * kko112.gram * Y = !![a + 2 * α ^ 2, b + 2 * α * β; b + 2 * α * β, c + 2 * β ^ 2] := by
  obtain ⟨X, hX⟩ := h
  have hE : ∀ l m, (Xᵀ * K3.gram * X) l m = tern1 a b c l m := fun l m => by rw [hX]; rfl
  -- the vector of norm 1
  have h22 := hE 2 2
  rw [K3_entry] at h22
  simp only [tern1] at h22
  norm_num at h22
  set u : Fin 3 → ℤ := fun i => X (.inl i) 2 with hu
  have hw : X (.inr 0) 2 = 0 ∧ X (.inr 1) 2 = 0 := by
    have hA : 0 ≤ X (.inr 0) 2 ^ 2 - X (.inr 0) 2 * X (.inr 1) 2 + X (.inr 1) 2 ^ 2 := by
      nlinarith [sq_nonneg (X (.inr 0) 2 - X (.inr 1) 2), sq_nonneg (X (.inr 0) 2), sq_nonneg (X (.inr 1) 2)]
    have hs := sq_nonneg (X (.inl 0) 2); have hs1 := sq_nonneg (X (.inl 1) 2); have hs2 := sq_nonneg (X (.inl 2) 2)
    simp only [a2f] at h22
    have h0 : X (.inr 0) 2 ^ 2 - X (.inr 0) 2 * X (.inr 1) 2 + X (.inr 1) 2 ^ 2 = 0 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (2 * X (.inr 0) 2 - X (.inr 1) 2), sq_nonneg (X (.inr 1) 2),
      sq_nonneg (2 * X (.inr 1) 2 - X (.inr 0) 2), sq_nonneg (X (.inr 0) 2)]
  have hu1 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    simp only [hu, a2f, hw.1, hw.2] at h22 ⊢; nlinarith
  -- `u = ± eᵢ`
  obtain ⟨i, hi, hio⟩ : ∃ i : Fin 3, u i ^ 2 = 1 ∧ u (oth i 0) = 0 ∧ u (oth i 1) = 0 := by
    have p0 := sq_nonneg (u 0); have p1 := sq_nonneg (u 1); have p2 := sq_nonneg (u 2)
    have z : ∀ t : ℤ, t ^ 2 = 0 → t = 0 := fun t ht => pow_eq_zero_iff two_ne_zero |>.mp ht
    by_cases h0 : u 0 = 0
    · by_cases h1 : u 1 = 0
      · refine ⟨2, by rw [h0, h1] at hu1; linarith, h0, h1⟩
      · have : u 1 ^ 2 ≥ 1 := by have := pow_pos (abs_pos.mpr h1) 2; rw [sq_abs] at this; omega
        refine ⟨1, by nlinarith, h0, z _ (by show u 2 ^ 2 = 0; nlinarith)⟩
    · have : u 0 ^ 2 ≥ 1 := by have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; omega
      refine ⟨0, by nlinarith, z _ (by simp [oth]; nlinarith), z _ (by simp [oth]; nlinarith)⟩
  have hui : u i ≠ 0 := fun h => by rw [h] at hi; norm_num at hi
  -- the columns `0, 1` are orthogonal to `u`, so their `i`-th coordinate vanishes
  have horth : ∀ l : Fin 2, X (.inl i) (Fin.castSucc l) = 0 := by
    intro l
    have h := hE (Fin.castSucc l) 2
    rw [K3_entry] at h
    have hz : tern1 a b c (Fin.castSucc l) 2 = 0 := by fin_cases l <;> rfl
    rw [hz] at h
    simp only [a2f, hw.1, hw.2, mul_zero, sub_zero, add_zero] at h
    have hs := sum3_split (fun j => X (.inl j) (Fin.castSucc l) * X (.inl j) 2) i
    rw [hs] at h
    have e0 : X (.inl (oth i 0)) 2 = 0 := hio.1
    have e1 : X (.inl (oth i 1)) 2 = 0 := hio.2
    rw [e0, e1, mul_zero, mul_zero, add_zero, add_zero] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hui
  -- the representation
  let v : Fin 2 → ℤ := ![α, β]
  refine ⟨Matrix.of fun r l => match r with
    | .inl 0 => X (.inl (oth i 0)) (Fin.castSucc l)
    | .inl 1 => X (.inl (oth i 1)) (Fin.castSucc l)
    | .inl 2 => v l
    | .inr j => X (.inr j) (Fin.castSucc l), ?_⟩
  ext l m
  rw [kko112_entry]
  have hlm := hE (Fin.castSucc l) (Fin.castSucc m)
  rw [K3_entry] at hlm
  have hs := sum3_split (fun j => X (.inl j) (Fin.castSucc l) * X (.inl j) (Fin.castSucc m)) i
  rw [hs, horth l, zero_mul, zero_add] at hlm
  simp only [Matrix.of_apply]
  have key : X (.inl (oth i 0)) (Fin.castSucc l) * X (.inl (oth i 0)) (Fin.castSucc m) +
      X (.inl (oth i 1)) (Fin.castSucc l) * X (.inl (oth i 1)) (Fin.castSucc m) +
      a2f (X (.inr 0) (Fin.castSucc l)) (X (.inr 1) (Fin.castSucc l)) (X (.inr 0) (Fin.castSucc m))
        (X (.inr 1) (Fin.castSucc m)) = tern1 a b c (Fin.castSucc l) (Fin.castSucc m) := by
    rw [← hlm]
  fin_cases l <;> fin_cases m <;> simp [v, tern1] at key ⊢ <;> linarith

end KimKimOh.Kko112

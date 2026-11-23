import KimKimOh.Loops
import KimKimOh.WindowBound
import KimKimOh.Compute.Pass

/-!
# The kernel test of a binary block in the first pass

`blockOK s wt2 wt3 a b c` tries the directions `dirsFP` in order. For a direction it reads the
steps `w₂, w₃` of `k` from the tables, computes `Δ = δ - s αᵀ adj(B) α` in `ℕ`, and searches a
window `G` with `ubound Δ δ cnt G < G` while `s a (w₂ w₃ G)² < 3 Δ` (`dirOK`). By `block_rep` and
`sum_le_ubound`, a block that passes is represented, for every maximal reduced completion
(`blockOK_sound`).
-/

namespace KimKimOh

open GramLattice Tables

/-! ### Soundness -/

theorem winIter_spec {pos : ℕ → Bool} {u : ℕ → ℕ} : ∀ (fuel g : ℕ), 0 < g →
    winIter pos u fuel g = true → ∃ G, 0 < G ∧ pos G = true ∧ u G < G
  | 0, g, _, h => by simp [winIter] at h
  | fuel + 1, g, hg, h => by
    simp only [winIter, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at h
    obtain ⟨hp, hu | hr⟩ := h
    · exact ⟨g, hg, hp, hu⟩
    · exact winIter_spec fuel (u g + 1) (by omega) hr

theorem dirsFP_gcd : ∀ d ∈ dirsFP, Nat.gcd d.1 d.2.1 = 1 ∨ Nat.gcd d.1 d.2.1 = 2 ∨
    Nat.gcd d.1 d.2.1 = 3 ∨ Nat.gcd d.1 d.2.1 = 4 ∨ Nat.gcd d.1 d.2.1 = 6 := by
  decide

theorem dirsFP_coprime {d : ℕ × ℕ × Bool} (hd : d ∈ dirsFP) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ ((p : ℤ) ∣ (d.1 : ℤ) ∧ (p : ℤ) ∣ dirY d) := by
  rintro ⟨h1, h2⟩
  have h1' : p ∣ d.1 := Int.natCast_dvd_natCast.mp h1
  have h2' : p ∣ d.2.1 := by
    unfold dirY at h2
    split_ifs at h2
    · exact Int.natCast_dvd_natCast.mp (dvd_neg.mp h2)
    · exact Int.natCast_dvd_natCast.mp h2
  have hg := Nat.dvd_gcd h1' h2'
  have hgle : Nat.gcd d.1 d.2.1 ≤ 6 ∧ Nat.gcd d.1 d.2.1 ≠ 5 ∧ 0 < Nat.gcd d.1 d.2.1 := by
    rcases dirsFP_gcd d hd with h | h | h | h | h <;> rw [h] <;> norm_num
  have hle := Nat.le_of_dvd hgle.2.2 hg
  have hp6 : p = 5 ∨ p = 6 := by omega
  rcases hp6 with rfl | rfl
  · obtain ⟨q, hq⟩ := hg; omega
  · norm_num at hp

theorem r4_dirY (d : ℕ × ℕ × Bool) : r4 (dirY d) = resY 4 d := by
  unfold r4 dirY resY
  cases d.2.2 <;> simp <;> omega

theorem rp3_dirY (d : ℕ × ℕ × Bool) : rp 3 (dirY d) = resY 3 d := by
  unfold rp dirY resY
  cases d.2.2 <;> simp <;> omega

/-- `c x² - 2 b x y + a y² ≥ 0` for `a > 0` and `b² ≤ a c`, since
`a (c x² - 2 b x y + a y²) = (a y - b x)² + (a c - b²) x²`. -/
theorem quad_nonneg {a b c : ℤ} (ha : 0 < a) (hδ : b * b ≤ a * c) (x y : ℤ) :
    0 ≤ c * x * x - 2 * b * x * y + a * y * y := by
  refine (mul_nonneg_iff_of_pos_left ha).mp ?_
  have h1 : 0 ≤ a * c - b * b := by linarith
  nlinarith [sq_nonneg (a * y - b * x), mul_nonneg h1 (mul_self_nonneg x)]

theorem quad_nonneg_natCast {a b c : ℕ} (ha : 0 < a) (hδ : b * b < a * c) (x : ℕ) (y : ℤ) :
    0 ≤ (c : ℤ) * x * x - 2 * b * x * y + a * y * y :=
  quad_nonneg (by exact_mod_cast ha) (by exact_mod_cast hδ.le) x y

/-- `αᵀ adj(B) α` in `ℕ` for a positive definite block. -/
theorem bfN_eq {a b c : ℕ} (ha : 0 < a) (hδ : b * b < a * c) (d : ℕ × ℕ × Bool) :
    (bfN a b c d : ℤ) = c * d.1 * d.1 - 2 * b * d.1 * dirY d + a * dirY d * dirY d := by
  unfold bfN dirY
  cases h : d.2.2
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    have hle : 2 * b * d.1 * d.2.1 ≤ c * d.1 * d.1 + a * d.2.1 * d.2.1 := by
      have := quad_nonneg_natCast ha hδ d.1 d.2.1
      have h2 : ((2 * b * d.1 * d.2.1 : ℕ) : ℤ) ≤ ((c * d.1 * d.1 + a * d.2.1 * d.2.1 : ℕ) : ℤ) := by
        push_cast; linarith
      exact_mod_cast h2
    push_cast [hle]
    ring
  · simp only [Bool.cond_true, ite_true]
    push_cast
    ring

theorem weight_eq (g : Tern) {a b c δ : ℕ} (ha : g.a = a) (hb : g.b = b) (hc : g.c = c)
    (hδ : g.delta = δ) (p : ℕ) : g.weight p = wtN δ (Nat.gcd a (Nat.gcd b c)) p := by
  unfold Tern.weight wtN
  rw [ha, hb, hc, hδ]
  simp only [Int.natCast_dvd_natCast]
  have hgcd : (p ∣ a ∧ p ∣ b ∧ p ∣ c) ↔ p ∣ Nat.gcd a (Nat.gcd b c) := by
    rw [Nat.dvd_gcd_iff, Nat.dvd_gcd_iff]
  by_cases h1 : p ∣ δ <;> by_cases h2 : p ∣ a ∧ p ∣ b ∧ p ∣ c
  · simp [h1, h2, Nat.mod_eq_zero_of_dvd h1, Nat.mod_eq_zero_of_dvd (hgcd.mp h2)]
  · simp only [h1, h2, not_false_eq_true, and_self, ite_true]
    have : ¬ Nat.gcd a (Nat.gcd b c) % p = 0 := fun h => h2 (hgcd.mpr (Nat.dvd_of_mod_eq_zero h))
    simp [Nat.mod_eq_zero_of_dvd h1, this]
  · simp only [h1, false_and, ite_false]
    have : ¬ δ % p = 0 := fun h => h1 (Nat.dvd_of_mod_eq_zero h)
    simp [this]
  · simp only [h1, false_and, ite_false]
    have : ¬ δ % p = 0 := fun h => h1 (Nat.dvd_of_mod_eq_zero h)
    simp [this]

theorem rowOf_wget (wt blk i : ℕ) (hi : i < 16) : (rowOf wt blk >>> (4 * i)) &&& 15 = wget wt blk i := by
  unfold rowOf wget
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 4
  · have : 4 * i + j < 64 := by omega
    simp [this, Nat.add_assoc]
  · have h15 : (15 : ℕ).testBit j = false := by
      apply Nat.testBit_lt_two_pow
      calc 15 < 2 ^ 4 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [h15]

theorem gs_ge_five {Δ : ℕ} (h : Nat.gcd Δ prim47 ≠ 1) : 5 ≤ Nat.gcd Δ prim47 := by
  have hd := Nat.gcd_dvd_right Δ prim47
  have hpos : 0 < Nat.gcd Δ prim47 := Nat.gcd_pos_of_pos_right _ (by decide)
  by_contra hlt
  push Not at hlt
  interval_cases h' : Nat.gcd Δ prim47
  · exact h rfl
  all_goals revert hd; decide

/-- **The fast window is a window.** -/
theorem fastG_spec {Δ δ cnt : ℕ} (hΔ : 0 < Δ) (h5 : fastG Δ δ ≤ 5) :
    ubound Δ δ cnt (fastG Δ δ) < fastG Δ δ := by
  set gs := Nat.gcd Δ prim47 with hgs
  have hc : Nat.blt gs 35 = true ∧ Nat.blt (Nat.gcd Δ δ) 5 = true := by
    unfold fastG at h5
    rw [← hgs] at h5
    cases hA : Nat.blt gs 35 <;> cases hB : Nat.blt (Nat.gcd Δ δ) 5 <;> simp [hA, hB] at h5 ⊢
  have hfast : fastG Δ δ = cond (Nat.beq gs 1) 1 2 + largeBound (Δ / gs) := by
    unfold fastG; rw [← hgs, hc.1, hc.2]; rfl
  have hgs35 : gs < 35 := Nat.blt_eq.mp hc.1
  have hg5 : Nat.gcd Δ δ < 5 := Nat.blt_eq.mp hc.2
  rw [hfast] at h5 ⊢
  unfold ubound
  rw [← hgs, recsum_eq]
  have hLB0 : largeBound (Nat.gcd Δ δ) = 0 := by
    unfold largeBound; rw [show Nat.blt (Nat.gcd Δ δ) 53 = true from Nat.blt_eq.mpr (by omega)]; rfl
  rw [hLB0, add_zero]
  by_cases h1 : gs = 1
  · have hb : Nat.beq gs 1 = true := by rw [h1]; rfl
    have hsm : smallOf gs = [] := by unfold smallOf; rw [h1]; rfl
    rw [hb, hsm]
    simp only [Bool.cond_true, List.map_nil, List.sum_nil, zero_add]
    have : (1 + largeBound (Δ / gs) + 52) / 53 = 1 := by omega
    rw [this]; omega
  · have hge : 5 ≤ gs := gs_ge_five h1
    have hb : Nat.beq gs 1 = false := beq_false_of_ne h1
    have hsm : smallOf gs = [gs] := by
      unfold smallOf
      rw [show (gs == 1) = false by simpa using h1, show Nat.blt gs 35 = true from hc.1]
      rfl
    have hwt : wtN δ cnt gs = 1 := by
      unfold wtN
      have : ¬ δ % gs = 0 := by
        intro h0
        have hdvd : gs ∣ Nat.gcd Δ δ := Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (Nat.dvd_of_mod_eq_zero h0)
        have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hΔ) hdvd
        omega
      simp [this]
    rw [hb, hsm]
    simp only [Bool.cond_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hwt, one_mul]
    rw [hb] at h5
    simp only [Bool.cond_false] at h5
    have e1 : (2 + largeBound (Δ / gs) + gs - 1) / gs = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have e2 : (2 + largeBound (Δ / gs) + 52) / 53 = 1 := by omega
    rw [e1, e2]
    omega

/-! ### The block of a ternary -/

theorem r8_natCast (n : ℕ) : r8 (n : ℤ) = n % 8 := by unfold r8; omega
theorem r4_natCast (n : ℕ) : r4 (n : ℤ) = n % 4 := by unfold r4; omega
theorem r9_natCast (n : ℕ) : r9 (n : ℤ) = n % 9 := by unfold r9; omega

/-- The chunk at 2 of a ternary with diagonal block `(a, b, c)`. -/
theorem chunk2_eq {g : Tern} {a b c : ℕ} (ha : g.a = a) (hb : g.b = b) (hc : g.c = c) :
    chunk2 g = blk2 (a % 8) (b % 4) (c % 8) := by
  rw [chunk2, ha, hb, hc, r8_natCast, r4_natCast, r8_natCast]

/-- The chunk at 3 of a ternary with diagonal block `(a, b, c)`. -/
theorem chunk3_eq {g : Tern} {a b c : ℕ} (ha : g.a = a) (hb : g.b = b) (hc : g.c = c) :
    chunk3 g = blk3 (a % 9) (b % 9) (c % 9) := by
  rw [chunk3, ha, hb, hc, r9_natCast, r9_natCast, r9_natCast]

/-- `δ = a c - b²` for the block `(a, b, c)` of `S`, as a natural number. -/
theorem delta_natCast (S : GramLattice (Fin 3)) {a b c : ℕ} (ha : (ternOf S).a = a)
    (hb : (ternOf S).b = b) (hc : (ternOf S).c = c) :
    b * b < a * c ∧ (ternOf S).delta = ((a * c - b * b : ℕ) : ℤ) := by
  have hδ0 := delta_pos S
  have e : (ternOf S).delta = (a : ℤ) * c - b * b := by simp only [Tern.delta, ha, hb, hc]
  have hbc : b * b < a * c := by
    have : ((b * b : ℕ) : ℤ) < ((a * c : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  exact ⟨hbc, by rw [e]; push_cast [hbc.le]; ring⟩

/-- **Soundness of the first-pass test.** If the block `(a, b, c)` passes, then `L` represents
every maximal ternary with this block in a reduced basis. -/
theorem blockOK_sound (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (ht2 : tableOK2 H.wt2 = true) (ht3 : tableOK3 H.wt3 = true)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) (hred : (ternOf S).IsReduced)
    {a b c : ℕ} (ha : (ternOf S).a = a) (hb : (ternOf S).b = b) (hc : (ternOf S).c = c)
    (h : blockOK H.s H.wt2 H.wt3 a b c = true) : L.Represents S := by
  have ha0 : 0 < a := by have := a_pos S; rw [ha] at this; exact_mod_cast this
  have hδ0 := delta_pos S
  obtain ⟨hbc, hδeq⟩ := delta_natCast S ha hb hc
  set g := ternOf S with hg
  obtain ⟨d', hd', hdir⟩ := anyR_spec h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
  unfold dirOK at hdir
  simp only [Bool.and_eq_true, Nat.blt_eq] at hdir
  obtain ⟨⟨hm13, hlt⟩, hwin⟩ := hdir
  set blk2' := blk2 (a % 8) (b % 4) (c % 8) with hblk2'
  set blk3' := blk3 (a % 9) (b % 9) (c % 9) with hblk3'
  set i2 := 4 * (d.1 % 4) + resY 4 d with hi2def
  set i3 := 3 * (d.1 % 3) + resY 3 d with hi3def
  have hi2 : i2 < 16 := by
    have : resY 4 d < 4 := by unfold resY; cases d.2.2 <;> simp <;> omega
    omega
  have hi3 : i3 < 9 := by
    have : resY 3 d < 3 := by unfold resY; cases d.2.2 <;> simp <;> omega
    omega
  rw [rowOf_wget _ _ _ hi2, rowOf_wget _ _ _ (by omega)] at hm13 hwin
  set w₂ := wget H.wt2 blk2' i2 with hw₂def
  set w₃ := wget H.wt3 blk3' i3 with hw₃def
  -- the table values
  have hv2 : w₂ = 1 ∨ w₂ = 2 ∨ w₂ = 4 ∨ w₂ = 15 := by
    unfold tableOK2 at ht2
    rw [List.all_eq_true] at ht2
    have hb2 : blk2' < 256 := by simp only [hblk2', blk2]; omega
    have := ht2 blk2' (List.mem_range.mpr hb2)
    rw [List.all_eq_true] at this
    have := this i2 (List.mem_range.mpr hi2)
    simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using this
  have hv3 : w₃ = 1 ∨ w₃ = 3 ∨ w₃ = 15 := by
    unfold tableOK3 at ht3
    rw [List.all_eq_true] at ht3
    have hb3 : blk3' < 729 := by simp only [hblk3', blk3]; omega
    have := ht3 blk3' (List.mem_range.mpr hb3)
    rw [List.all_eq_true] at this
    have := this i3 (List.mem_range.mpr hi3)
    simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using this
  have hw₂ : w₂ = 1 ∨ w₂ = 2 ∨ w₂ = 4 := by
    rcases hv2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exfalso; rw [h] at hm13; rcases hv3 with h' | h' | h' <;> rw [h'] at hm13 <;> omega
  have hw₃ : w₃ = 1 ∨ w₃ = 3 := by
    rcases hv3 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso; rw [h] at hm13; rcases hw₂ with h' | h' | h' <;> rw [h'] at hm13 <;> omega
  -- the window
  set Δ : ℕ := a * c - b * b - H.s * bfN a b c (d.1, d.2.1, d.2.2) with hΔ
  have hd3 : (d.1, d.2.1, d.2.2) = d := rfl
  rw [hd3] at hlt hΔ
  obtain ⟨G, hG0, hpos, hub⟩ : ∃ G, 0 < G ∧ H.s * a * (w₂ * w₃ * G) ^ 2 < 3 * Δ ∧
      ubound Δ (a * c - b * b) (Nat.gcd a (Nat.gcd b c)) G < G := by
    unfold winOK at hwin
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hwin
    rcases hwin with ⟨h5, hp⟩ | hs
    · have hΔpos : 0 < Δ := by
        by_contra h0; push Not at h0
        have : Δ = 0 := by omega
        rw [this] at hp; omega
      refine ⟨fastG Δ (a * c - b * b), ?_, hp, fastG_spec hΔpos h5⟩
      have := fastG_spec (cnt := Nat.gcd a (Nat.gcd b c)) hΔpos h5
      omega
    · obtain ⟨G, hG, h1, h2⟩ := winIter_spec 16 1 (by norm_num) hs
      simp only [Nat.blt_eq] at h1
      exact ⟨G, hG, h1, h2⟩
  -- the direction
  set x : ℤ := ((d.1 : ℕ) : ℤ) with hx
  set y : ℤ := dirY d with hy
  have hch2 : chunk2 g = blk2' := chunk2_eq ha hb hc
  have hch3 : chunk3 g = blk3' := chunk3_eq ha hb hc
  have hi2' : 4 * r4 x + r4 y = i2 := by
    rw [hy, r4_dirY, hi2def]; simp only [hx, r4]; omega
  have hi3' : 3 * rp 3 x + rp 3 y = i3 := by
    rw [hy, rp3_dirY, hi3def]; simp only [hx, rp]; omega
  have hΔeq : g.corrDelta H.s x y = (Δ : ℤ) := by
    have hbf := bfN_eq ha0 hbc d
    rw [Tern.corrDelta, hδeq]
    simp only [ha, hb, hc]
    rw [hΔ]
    push_cast [hlt.le]
    rw [hbf]
  refine block_rep H hK L hL S hmax hred x y (fun p hp h5 => dirsFP_coprime hd hp h5)
    (by rw [hch2, hi2']; exact hw₂) (by rw [hch3, hi3']; exact hw₃) G hG0 ?_ ?_
  · -- the sieve sum
    have hΔpos : 0 < Δ := by
      by_contra h0
      push Not at h0
      have : Δ = 0 := by omega
      rw [this] at hpos
      omega
    rw [hΔeq]
    have hbig : bigPrimesOf (Δ : ℤ) = Δ.primeFactors.filter (5 ≤ ·) := by
      simp [bigPrimesOf]
    rw [hbig]
    have hw : ∀ p, (ternOf S).weight p = wtN (a * c - b * b) (Nat.gcd a (Nat.gcd b c)) p :=
      weight_eq (ternOf S) ha hb hc (by rw [← hg, hδeq])
    simp only [hw]
    exact (sum_le_ubound _ _ _ G hΔpos).trans_lt hub
  · rw [hch2, hi2', hch3, hi3', hΔeq, ha]
    exact_mod_cast hpos

end KimKimOh

import KimKimOh.Tables.Profiles3
import KimKimOh.MaximalMod

/-!
# The sets `𝒰_{j,2}(σ)` and the profiles at 2 (`app:correction-tests`, `app:prescriptions`)

As at 3 (`Profiles`), with residues `(a, 2b, c, 2d, 2e, f)` modulo 8, chunks `(a, b, c)` and
lifts of `z ∈ 𝔽₂³` modulo 4 (enough for both scales: `v² mod 8` and `vᵢvⱼ mod 4` only depend on
`v mod 4`). A residue is maximal at 2 exactly when `4 ∤ det` (`not_four_dvd_det_of_isMaximal`).
-/

namespace KimKimOh.Tables

open Matrix

/-- `(u - w) mod 8` and `(u - w) mod 4`. -/
def sub8 (u w : ℕ) : ℕ := (u + 8 - w % 8) % 8
def sub4 (u w : ℕ) : ℕ := (u + 4 - w % 4) % 4

/-- The chunk of `T - s vvᵀ` at 2. -/
def blkShift2 (s a b c v₀ v₁ : ℕ) : ℕ :=
  blk2 (sub8 a (s * v₀ * v₀)) (sub4 b (s * v₀ * v₁)) (sub8 c (s * v₁ * v₁))

/-- The 8 lifts modulo 4 of `z ∈ 𝔽₂³`. -/
def lifts2 (z₀ z₁ z₂ : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range 2).flatMap fun w₀ => (List.range 2).flatMap fun w₁ => (List.range 2).map fun w₂ =>
    (z₀ + 2 * w₀, z₁ + 2 * w₁, z₂ + 2 * w₂)

/-- All 128 bits. -/
def full128 : ℕ := 2 ^ 128 - 1

/-- The residues of the chunk `(a, b, c)` at which `z` is permissible at 2. -/
def perm2 (acc : BT ℕ) (s a b c z₀ z₁ z₂ : ℕ) : ℕ :=
  (lifts2 z₀ z₁ z₂).foldl (fun m v => m &&& tr2 (acc.get 0 8 (blkShift2 s a b c v.1 v.2.1))
    (s * v.1 * v.2.2) (s * v.2.1 * v.2.2) (s * v.2.2 * v.2.2)) full128

/-- The 8 permissible sets of a chunk, at index `4 x + 2 y + k`. -/
def perms2 (acc : BT ℕ) (s a b c : ℕ) : List ℕ :=
  [0, 1].flatMap fun x => [0, 1].flatMap fun y => [0, 1].map fun k => perm2 acc s a b c x y k

def get2 (ps : List ℕ) (x y k : ℕ) : ℕ := ps.getD (4 * x + 2 * y + k) 0

/-- `det mod 4` from the residue digits. -/
def det4 (a b c d e f : ℕ) : ℕ :=
  (a * c * f + 2 * b * d * e + 3 * (a * e * e + c * d * d + f * b * b)) % 4

/-- The residues of the chunk `(a, b, c)` accepted after the correction by `v = (x, y, k)`
modulo 4 (no lifts). -/
def fine2 (acc : BT ℕ) (s a b c x y k : ℕ) : ℕ :=
  tr2 (acc.get 0 8 (blkShift2 s a b c x y)) (s * x * k) (s * y * k) (s * k * k)

/-- The residues at which the direction `(x, y)` modulo 4 has `k`-step `w` at 2: all `k` modulo 4
for `w = 1`, a class modulo 2 for `w = 2`, some `k` for `w = 4` (no condition otherwise). -/
def stepSet2 (acc : BT ℕ) (s a b c x y w : ℕ) : ℕ :=
  if w == 1 then fine2 acc s a b c x y 0 &&& fine2 acc s a b c x y 1 &&& fine2 acc s a b c x y 2 &&&
    fine2 acc s a b c x y 3
  else if w == 2 then (fine2 acc s a b c x y 0 &&& fine2 acc s a b c x y 2) |||
    (fine2 acc s a b c x y 1 &&& fine2 acc s a b c x y 3)
  else if w == 4 then fine2 acc s a b c x y 0 ||| fine2 acc s a b c x y 1 |||
    fine2 acc s a b c x y 2 ||| fine2 acc s a b c x y 3
  else full128

/-- **The kernel check of profiles and steps on one chunk at 2.** -/
def profChunkOK2 (acc : BT ℕ) (s : ℕ) (profs : ℕ → List (List (List (ℕ × ℕ)))) (pm wt blk : ℕ) :
    Bool :=
  (List.range 128).all fun l =>
    ((List.range 16).foldl (fun m i => m &&&
        stepSet2 acc s (blk / 32) (blk / 8 % 4) (blk % 8) (i / 4) (i % 4) (wget wt blk i))
      (profU 2 full128 (get2 (perms2 acc s (blk / 32) (blk / 8 % 4) (blk % 8)))
        (maskedProfs (profs (blk / 32 % 4)) (mget pm blk)))).testBit l ||
    det4 (blk / 32) (blk / 8 % 4) (blk % 8) (l / 32) (l / 8 % 4) (l % 8) == 0

/-! ### Semantics -/

theorem r8_sub (u w : ℤ) : r8 (u - w) = sub8 (r8 u) (r8 w) := by unfold r8 sub8; omega
theorem r4_sub (u w : ℤ) : r4 (u - w) = sub4 (r4 u) (r4 w) := by unfold r4 sub4; omega

theorem r8_sq (s : ℕ) (x : ℤ) : r8 (s * x * x) = (s * r4 x * r4 x) % 8 := by
  have hx : ((r4 x : ℕ) : ℤ) = x % 4 := by unfold r4; omega
  have h : x % 4 + 4 * (x / 4) = x := by omega
  have e : s * x * x - s * (x % 4) * (x % 4) =
      8 * (s * ((x % 4) * (x / 4) + 2 * (x / 4) * (x / 4))) := by
    linear_combination (-(s : ℤ) * (x + x % 4 + 4 * (x / 4))) * h
  have hm : (s * (x % 4) * (x % 4)) % 8 = (s * x * x) % 8 :=
    Int.modEq_iff_dvd.mpr ⟨_, e⟩
  have : ((s * r4 x * r4 x % 8 : ℕ) : ℤ) = (s * x * x) % 8 := by
    push_cast; rw [hx, hm]
  have h2 : ((r8 (s * x * x) : ℕ) : ℤ) = (s * x * x) % 8 := by unfold r8; omega
  exact_mod_cast h2.trans this.symm

theorem r4_mul (s : ℕ) (x y : ℤ) : r4 (s * x * y) = (s * r4 x * r4 y) % 4 := by
  have hx : ((r4 x : ℕ) : ℤ) = x % 4 := by unfold r4; omega
  have hy : ((r4 y : ℕ) : ℤ) = y % 4 := by unfold r4; omega
  have hm : (s * (x % 4) * (y % 4)) % 4 = (s * x * y) % 4 :=
    ((Int.mod_modEq x 4).mul_left _).mul (Int.mod_modEq y 4)
  have : ((s * r4 x * r4 y % 4 : ℕ) : ℤ) = (s * x * y) % 4 := by
    push_cast; rw [hx, hy, hm]
  have h2 : ((r4 (s * x * y) : ℕ) : ℤ) = (s * x * y) % 4 := by unfold r4; omega
  exact_mod_cast h2.trans this.symm

theorem accepted2_corr (acc : BT ℕ) (g : Tern) (s : ℕ) (x y k : ℤ) :
    accepted2 acc (g.corr s x y k) =
      (acc.get 0 8 (blkShift2 s (r8 g.a) (r4 g.b) (r8 g.c) (r4 x) (r4 y))).testBit
        (loc2 (sub4 (r4 g.d) (s * r4 x * r4 k)) (sub4 (r4 g.e) (s * r4 y * r4 k))
          (sub8 (r8 g.f) (s * r4 k * r4 k))) := by
  unfold accepted2 blkShift2
  simp only [Tern.corr, r8_sub, r4_sub, r8_sq, r4_mul, sub8, sub4, Nat.mod_mod]

/-- **A permissible direction at 2.** -/
theorem accepted_of_perm2 (acc : BT ℕ) (s : ℕ) (g : Tern) (x y k : ℤ)
    (h : (perm2 acc s (r8 g.a) (r4 g.b) (r8 g.c) (rp 2 x) (rp 2 y) (rp 2 k)).testBit
      (loc2 (r4 g.d) (r4 g.e) (r8 g.f)) = true) :
    accepted2 acc (g.corr s x y k) = true := by
  unfold perm2 at h
  obtain ⟨-, hall⟩ := testBit_foldl_and _ _ _ _ h
  have e : ∀ z, r4 z = rp 2 z + 2 * (r4 z / 2) ∧ r4 z / 2 < 2 := by
    intro z; unfold r4 rp; omega
  have hmem : (r4 x, r4 y, r4 k) ∈ lifts2 (rp 2 x) (rp 2 y) (rp 2 k) := by
    obtain ⟨ex, ex'⟩ := e x; obtain ⟨ey, ey'⟩ := e y; obtain ⟨ek, ek'⟩ := e k
    simp only [lifts2, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    exact ⟨r4 x / 2, ex', r4 y / 2, ey', r4 k / 2, ek', ex.symm, ey.symm, ek.symm⟩
  have := hall _ hmem
  simp only at this
  rw [testBit_tr2 _ _ _ _ (r4_lt _) (r4_lt _) (r8_lt _)] at this
  rw [accepted2_corr]
  unfold sub4 sub8
  exact this

theorem get2_perms2 (acc : BT ℕ) (s a b c : ℕ) {x y k : ℕ} (hx : x < 2) (hy : y < 2)
    (hk : k < 2) : get2 (perms2 acc s a b c) x y k = perm2 acc s a b c x y k := by
  interval_cases x <;> interval_cases y <;> interval_cases k <;> rfl

theorem cast_r8_four (z : ℤ) : ((r8 z : ℕ) : ZMod 4) = (z : ZMod 4) := by
  have h : ((r8 z : ℕ) : ℤ) = z % 4 + 4 * ((z % 8) / 4) := by unfold r8; omega
  rw [← Int.cast_natCast, h]
  push_cast
  rw [show (4 : ZMod 4) = 0 from rfl, zero_mul, add_zero]
  exact_mod_cast ZMod.intCast_mod z 4

theorem cast_r4_four (z : ℤ) : ((r4 z : ℕ) : ZMod 4) = (z : ZMod 4) := by
  have h : ((r4 z : ℕ) : ℤ) = z % 4 := by unfold r4; omega
  rw [← Int.cast_natCast, h]
  exact_mod_cast ZMod.intCast_mod z 4

/-- **A maximal ternary has `det ≢ 0 (mod 4)`, residue by residue.** -/
theorem det4_ne_zero (g : Tern) (hmax : IsMaximal g.toMatrix) :
    det4 (r8 g.a) (r4 g.b) (r8 g.c) (r4 g.d) (r4 g.e) (r8 g.f) ≠ 0 := by
  intro h0
  have hsym : ∀ i j, g.toMatrix i j = g.toMatrix j i := by
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  have hnd := not_four_dvd_det_of_isMaximal hmax hsym
  rw [Tern.ofMatrix_toMatrix] at hnd
  apply hnd
  have hz : ((det4 (r8 g.a) (r4 g.b) (r8 g.c) (r4 g.d) (r4 g.e) (r8 g.f) : ℕ) : ZMod 4) = 0 := by
    rw [h0]; rfl
  unfold det4 at hz
  rw [ZMod.natCast_mod] at hz
  push_cast at hz
  simp only [cast_r8_four, cast_r4_four] at hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
  unfold Tern.det Tern.delta
  push_cast
  have h4 : (4 : ZMod 4) = 0 := rfl
  linear_combination hz - ((g.a : ZMod 4) * g.e * g.e + g.c * g.d * g.d + g.f * g.b * g.b) * h4

/-- The chunk of a ternary at 2. -/
def chunk2 (g : Tern) : ℕ := blk2 (r8 g.a) (r4 g.b) (r8 g.c)

theorem accepted_of_fine2 (acc : BT ℕ) (s : ℕ) (g : Tern) (x y k : ℤ)
    (h : (fine2 acc s (r8 g.a) (r4 g.b) (r8 g.c) (r4 x) (r4 y) (r4 k)).testBit
      (loc2 (r4 g.d) (r4 g.e) (r8 g.f)) = true) :
    accepted2 acc (g.corr s x y k) = true := by
  unfold fine2 at h
  rw [testBit_tr2 _ _ _ _ (r4_lt _) (r4_lt _) (r8_lt _)] at h
  rw [accepted2_corr]
  unfold sub4 sub8
  exact h

theorem stepSet2_spec {acc : BT ℕ} {s a b c x y w l : ℕ}
    (h : (stepSet2 acc s a b c x y w).testBit l = true) (hw : w = 1 ∨ w = 2 ∨ w = 4) :
    ∃ k₀ < 4, ∀ k < 4, (w ∣ (k + 4 - k₀)) → (fine2 acc s a b c x y k).testBit l = true := by
  unfold stepSet2 at h
  rcases hw with rfl | rfl | rfl
  · simp only [beq_self_eq_true, ite_true, Nat.testBit_and, Bool.and_eq_true] at h
    exact ⟨0, by norm_num, fun k hk _ => by interval_cases k <;> simp_all⟩
  · simp only [show ((2 : ℕ) == 1) = false from rfl, beq_self_eq_true, ite_true,
      Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true,
      Bool.and_eq_true] at h
    rcases h with ⟨h0, h2⟩ | ⟨h1, h3⟩
    · exact ⟨0, by norm_num, fun k hk hd => by
        interval_cases k <;> simp_all⟩
    · exact ⟨1, by norm_num, fun k hk hd => by
        interval_cases k <;> simp_all⟩
  · simp only [show ((4 : ℕ) == 1) = false from rfl, show ((4 : ℕ) == 2) = false from rfl,
      beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,
      Bool.or_eq_true] at h
    have key : ∀ k₀ < 4, (fine2 acc s a b c x y k₀).testBit l = true →
        ∃ k₀ < 4, ∀ k < 4, (4 ∣ (k + 4 - k₀)) → (fine2 acc s a b c x y k).testBit l = true :=
      fun k₀ hk₀ hb => ⟨k₀, hk₀, fun k hk hd => by
        have : k = k₀ := by omega
        rw [this]; exact hb⟩
    rcases h with ((h | h) | h) | h
    · exact key 0 (by norm_num) h
    · exact key 1 (by norm_num) h
    · exact key 2 (by norm_num) h
    · exact key 3 (by norm_num) h

/-- **The profiles and the `k`-steps at 2.** -/
theorem chunk2_spec (acc : BT ℕ) (s : ℕ) (profs : ℕ → List (List (List (ℕ × ℕ)))) (pm wt : ℕ)
    (hOK : ∀ blk < 256, profChunkOK2 acc s profs pm wt blk = true) (g : Tern)
    (hmax : IsMaximal g.toMatrix) :
    (∃ P ∈ maskedProfs (profs (r8 g.a % 4)) (mget pm (chunk2 g)), ∀ x : ℤ,
      ∀ o ∈ P.getD (rp 2 x) [],
        OptHolds (fun y k => accepted2 acc (g.corr s x y k) = true) (normOpt 2 o).1
          (normOpt 2 o).2) ∧
    ∀ x y : ℤ, (wget wt (chunk2 g) (4 * r4 x + r4 y) = 1 ∨ wget wt (chunk2 g) (4 * r4 x + r4 y) = 2 ∨
        wget wt (chunk2 g) (4 * r4 x + r4 y) = 4) →
      ∃ k₀ : ℤ, ∀ k : ℤ, (wget wt (chunk2 g) (4 * r4 x + r4 y) : ℤ) ∣ k - k₀ →
        accepted2 acc (g.corr s x y k) = true := by
  have ha := r8_lt g.a; have hb := r4_lt g.b; have hc := r8_lt g.c
  have hd := r4_lt g.d; have he := r4_lt g.e; have hf := r8_lt g.f
  set blk := chunk2 g with hblk
  set l := loc2 (r4 g.d) (r4 g.e) (r8 g.f) with hl
  have hblk' : blk < 256 := by simp only [hblk, chunk2, blk2]; omega
  have hl' : l < 128 := by simp only [hl, loc2]; omega
  have e1 : blk / 32 = r8 g.a := by simp only [hblk, chunk2, blk2]; omega
  have e2 : blk / 8 % 4 = r4 g.b := by simp only [hblk, chunk2, blk2]; omega
  have e3 : blk % 8 = r8 g.c := by simp only [hblk, chunk2, blk2]; omega
  have f1 : l / 32 = r4 g.d := by simp only [hl, loc2]; omega
  have f2 : l / 8 % 4 = r4 g.e := by simp only [hl, loc2]; omega
  have f3 : l % 8 = r8 g.f := by simp only [hl, loc2]; omega
  have hc2 := hOK blk hblk'
  unfold profChunkOK2 at hc2
  rw [List.all_eq_true] at hc2
  have hbit := hc2 l (List.mem_range.mpr hl')
  have hd4 : (det4 (r8 g.a) (r4 g.b) (r8 g.c) (r4 g.d) (r4 g.e) (r8 g.f) == 0) = false := by
    simpa using det4_ne_zero g hmax
  rw [e1, e2, e3, f1, f2, f3, hd4, Bool.or_false] at hbit
  obtain ⟨hU, hsteps⟩ := testBit_foldl_and _ _ _ _ hbit
  refine ⟨?_, fun x y hw => ?_⟩
  · obtain ⟨P, hP, hPbit⟩ := profU_spec hU
    refine ⟨P, hP, fun x o ho => ?_⟩
    refine optHolds_of_optSet (by norm_num)
      (profSet_spec hPbit (rp 2 x) (rp_lt (by norm_num) x) o ho) (fun y k hyk => ?_)
    rw [get2_perms2 _ _ _ _ _ (rp_lt (by norm_num) x) (rp_lt (by norm_num) y)
      (rp_lt (by norm_num) k)] at hyk
    exact accepted_of_perm2 acc s g x y k hyk
  · have hx := r4_lt x
    have hy := r4_lt y
    have hi : 4 * r4 x + r4 y < 16 := by omega
    have hs := hsteps _ (List.mem_range.mpr hi)
    rw [show (4 * r4 x + r4 y) / 4 = r4 x by omega,
      show (4 * r4 x + r4 y) % 4 = r4 y by omega] at hs
    obtain ⟨k₀, hk₀, hk⟩ := stepSet2_spec hs hw
    refine ⟨k₀, fun k hk' => accepted_of_fine2 acc s g x y k ?_⟩
    have hkr := r4_lt k
    refine hk _ hkr ?_
    -- `w ∣ k - k₀` with `w ∣ 4` gives `w ∣ r4 k + 4 - k₀`
    set w := wget wt blk (4 * r4 x + r4 y)
    have hw4 : (w : ℤ) ∣ 4 := by rcases hw with h | h | h <;> rw [h] <;> norm_num
    have hr : ((r4 k : ℕ) : ℤ) = k % 4 := by unfold r4; omega
    have : (w : ℤ) ∣ ((r4 k + 4 - k₀ : ℕ) : ℤ) := by
      have e : ((r4 k + 4 - k₀ : ℕ) : ℤ) = (k - k₀) + 4 * (1 - k / 4) := by
        push_cast [show k₀ ≤ r4 k + 4 by omega]; rw [hr]; have := Int.emod_add_mul_ediv k 4; linarith
      rw [e]; exact dvd_add hk' (dvd_mul_of_dvd_left hw4 _)
    exact_mod_cast this

end KimKimOh.Tables

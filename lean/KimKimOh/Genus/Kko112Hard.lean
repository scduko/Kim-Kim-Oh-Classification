import KimKimOh.Genus.Kko112HardLocal
import KimKimOh.Genus.Kko112Sieve
import KimKimOh.GramLattice.BinaryReduction

/-!
# Doubly hard binaries are represented by `⟨1, 1, 2⟩ ⊥ A₂` (Kim–Kim–Oh, §4)

`kko112_represents_hard`: `K₂₂` represents every positive binary `ℓ = [a, b, c]` with `a, c` even,
`b` odd and `ac - b² ≡ 1 (mod 3)`. After Gauss reduction, `0 ≤ 2b ≤ a ≤ c`, we find `v ∈ (3ℤ)²` with
`ℓ' = ℓ - 2 v vᵀ` positive and `ℓ' ≢ 0` modulo every prime `p ≥ 5`; then `K₂₂` represents `ℓ`
(`kko112_of_K3`, `locallyRepresents_K3_hard`). As in Kim–Kim–Oh:

* `a > 72`: `v = (3, -3s)` with `s` from the sieve (`Sieve.exists_shift`), so `ℓ' = [a - 18, b + 18s,
  c - 18s²]`; positivity is their Lemma 2.
* `a ≤ 72`, `ac - b² > 72a`: `v = (0, 3k)` for some `k ∈ {0, 1, 2}`; the primes `p ≥ 5` dividing
  `b ≤ 36` are at most two, and each excludes at most one `k`.
* `a ≤ 72`, `ac - b² ≤ 72a`, so `c ≤ 90`: a finite check by the kernel (`small_ok`), searching
  `v` in a box, and an explicit representation of `[10, 5, 20]`.
-/

open Matrix

namespace KimKimOh.Kko112

open Local LocalBinary GramLattice

/-! ### The shift -/

/-- **The shift.** If `ℓ' = [a', b', c']` satisfies the hypotheses of `locallyRepresents_K3_hard`,
then `K₂₂` represents `ℓ' + 2 v vᵀ`. -/
theorem rep_shift (a b c α β : ℤ) (ha : 0 < a) (hd : 0 < a * c - b * b) (ha2 : a % 2 = 0) (hb2 : b % 2 = 1)
    (hc2 : c % 2 = 0) (h3 : (a * c - b * b) % 3 = 1)
    (hprim : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) :
    ∃ Y : Matrix (Fin 3 ⊕ Fin 2) (Fin 2) ℤ,
      Yᵀ * kko112.gram * Y = !![a + 2 * α ^ 2, b + 2 * α * β; b + 2 * α * β, c + 2 * β ^ 2] :=
  kko112_of_K3 a b c ha hd α β (localGlobal_K3 (ternL a b c ha hd)
    fun p hp => locallyRepresents_K3_hard a b c ha2 hb2 hc2 h3 hprim p hp)

/-- No prime `p ≥ 5` divides all of `a, b, c` when their gcd divides `6²⁰`. -/
theorem prim_of_gcd (a b c : ℤ) (h : 6 ^ 20 % Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 0) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) := by
  rintro p hp h5 ⟨ha, hb, hc⟩
  have hg : p ∣ Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) :=
    Nat.dvd_gcd (Int.natCast_dvd.mp ha) (Nat.dvd_gcd (Int.natCast_dvd.mp hb) (Int.natCast_dvd.mp hc))
  have h6 : p ∣ 2 * 3 := hp.dvd_of_dvd_pow (hg.trans (Nat.dvd_of_mod_eq_zero h))
  rcases (Nat.Prime.dvd_mul hp).mp h6 with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := Nat.le_of_dvd (by norm_num) h3; omega

/-! ### `a > 72` -/

theorem rep_a_gt_72 (a b c : ℤ) (hb0 : 0 ≤ 2 * b) (hba : 2 * b ≤ a) (hac : a ≤ c) (ha2 : a % 2 = 0)
    (hb2 : b % 2 = 1) (hc2 : c % 2 = 0) (h3 : (a * c - b * b) % 3 = 1) (ha : 72 < a) :
    ∃ Y : Matrix (Fin 3 ⊕ Fin 2) (Fin 2) ℤ, Yᵀ * kko112.gram * Y = !![a, b; b, c] := by
  obtain ⟨s, hs, hsp⟩ := Sieve.exists_shift a b ha (Int.even_iff.mpr ha2)
  have habs := abs_nonneg s
  have hbs : 2 * b * s ≥ -(a * |s|) := by
    have h1 : -(2 * b * |s|) ≤ 2 * b * s := by
      have := neg_abs_le s
      nlinarith
    nlinarith
  have hd : 0 < (a - 18) * (c - 18 * s ^ 2) - (b + 18 * s) * (b + 18 * s) := by
    have hsq : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    have e : (a - 18) * (c - 18 * s ^ 2) - (b + 18 * s) * (b + 18 * s) =
        a * c - b * b - 18 * (a * s ^ 2 + 2 * b * s + c) := by ring
    rw [e]
    have h1 : 4 * (b * b) ≤ a * c := by nlinarith
    have h2 : a * s ^ 2 ≤ c * s ^ 2 := by nlinarith [sq_nonneg s]
    have h3' : a * |s| ≤ c * |s| := by nlinarith
    have h4 : 0 < c * (a - 24 * (s ^ 2 + |s| + 1)) := by nlinarith
    nlinarith
  obtain ⟨Y, hY⟩ := rep_shift (a - 18) (b + 18 * s) (c - 18 * s ^ 2) 3 (-3 * s) (by omega) hd (by omega) (by omega)
    (by have : (18 * s ^ 2) % 2 = 0 := by omega
        omega)
    (by have e : (a - 18) * (c - 18 * s ^ 2) - (b + 18 * s) * (b + 18 * s) =
            a * c - b * b - 3 * (6 * (a * s ^ 2 + 2 * b * s + c)) := by ring
        rw [e, Int.sub_mul_emod_self_left]; exact h3)
    (fun p hp h5 ⟨hpa, hpb, _⟩ => hsp p hp h5 hpa hpb)
  refine ⟨Y, hY.trans ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

/-! ### `a ≤ 72`, `ac - b² > 72 a` -/

theorem rep_det_gt_72a (a b c : ℤ) (hb0 : 0 ≤ 2 * b) (hba : 2 * b ≤ a) (ha2 : a % 2 = 0)
    (hb2 : b % 2 = 1) (hc2 : c % 2 = 0) (h3 : (a * c - b * b) % 3 = 1) (ha : a ≤ 72)
    (hd : 72 * a < a * c - b * b) :
    ∃ Y : Matrix (Fin 3 ⊕ Fin 2) (Fin 2) ℤ, Yᵀ * kko112.gram * Y = !![a, b; b, c] := by
  have ha0 : 0 < a := by omega
  -- some `k ∈ {0, 1, 2}` has `c - 18k²` prime to the primes `p ≥ 5` dividing `b`
  obtain ⟨k, hk, hkp⟩ : ∃ k : ℤ, 0 ≤ k ∧ k ≤ 2 ∧ ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ ((p : ℤ) ∣ b ∧ (p : ℤ) ∣ c - 18 * k ^ 2) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p0, hp0, h50, hb0', hc0'⟩ := hcon 0 le_rfl (by norm_num)
    obtain ⟨p1, hp1, h51, hb1', hc1'⟩ := hcon 1 (by norm_num) (by norm_num)
    obtain ⟨p2, hp2, h52, hb2', hc2'⟩ := hcon 2 (by norm_num) (by norm_num)
    have hne : ∀ (p q : ℕ) (i j : ℤ), p.Prime → 5 ≤ p → (p : ℤ) ∣ c - 18 * i ^ 2 → (q : ℤ) ∣ c - 18 * j ^ 2 →
        (18 * (j ^ 2 - i ^ 2)).natAbs = 18 ∨ (18 * (j ^ 2 - i ^ 2)).natAbs = 54 ∨ (18 * (j ^ 2 - i ^ 2)).natAbs = 72 →
        p ≠ q := by
      rintro p q i j hp h5 hpi hqj hm rfl
      have : (p : ℤ) ∣ 18 * (j ^ 2 - i ^ 2) := by
        have := dvd_sub hpi hqj
        have e : c - 18 * i ^ 2 - (c - 18 * j ^ 2) = 18 * (j ^ 2 - i ^ 2) := by ring
        rwa [e] at this
      exact not_dvd_of_dvd_two_three hp h5 (a := 3) (b := 3)
        (by rcases hm with h | h | h <;> rw [h] <;> norm_num) (Int.natCast_dvd.mp this)
    have h01 := hne p0 p1 0 1 hp0 h50 hc0' hc1' (by norm_num)
    have h02 := hne p0 p2 0 2 hp0 h50 hc0' hc2' (by norm_num)
    have h12 := hne p1 p2 1 2 hp1 h51 hc1' hc2' (by norm_num)
    -- three distinct primes `≥ 5` divide `b ≤ 36`
    have hb : b.natAbs ≤ 36 := by omega
    have hbne : b.natAbs ≠ 0 := by omega
    have d0 := Int.natCast_dvd.mp hb0'; have d1 := Int.natCast_dvd.mp hb1'; have d2 := Int.natCast_dvd.mp hb2'
    have c01 : Nat.Coprime p0 p1 := (Nat.coprime_primes hp0 hp1).mpr h01
    have c012 : Nat.Coprime (p0 * p1) p2 :=
      Nat.coprime_mul_iff_left.mpr ⟨(Nat.coprime_primes hp0 hp2).mpr h02, (Nat.coprime_primes hp1 hp2).mpr h12⟩
    have hdvd : p0 * p1 * p2 ∣ b.natAbs := c012.mul_dvd_of_dvd_of_dvd (c01.mul_dvd_of_dvd_of_dvd d0 d1) d2
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hbne) hdvd
    have : 125 ≤ p0 * p1 * p2 := by
      have := Nat.mul_le_mul (Nat.mul_le_mul h50 h51) h52
      omega
    omega
  obtain ⟨Y, hY⟩ := rep_shift a b (c - 18 * k ^ 2) 0 (3 * k) ha0
    (by have : k ^ 2 ≤ 4 := by nlinarith
        nlinarith)
    ha2 hb2 (by have : (18 * k ^ 2) % 2 = 0 := by omega
                omega)
    (by have e : a * (c - 18 * k ^ 2) - b * b = a * c - b * b - 3 * (6 * a * k ^ 2) := by ring
        rw [e, Int.sub_mul_emod_self_left]; exact h3)
    (fun p hp h5 ⟨_, hpb, hpc⟩ => hkp.2 p hp h5 ⟨hpb, hpc⟩)
  refine ⟨Y, hY.trans ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp
  ring

/-! ### `a ≤ 72`, `ac - b² ≤ 72 a`: a finite check -/

/-- The candidate vectors `v ∈ (3ℤ)²`. -/
def vbox : List (ℤ × ℤ) :=
  [(0, 0), (-3, 0), (0, -3), (0, 3), (3, 0), (-3, -3), (-3, 3), (3, -3), (3, 3), (-6, 0), (0, -6), (0, 6),
   (6, 0), (-6, -3), (-6, 3), (-3, -6), (-3, 6), (3, -6), (3, 6), (6, -3), (6, 3), (-9, 0), (-6, -6),
   (-6, 6), (0, -9), (0, 9), (6, -6), (6, 6), (9, 0), (-9, -3), (-9, 3), (-3, -9), (-3, 9), (3, -9),
   (3, 9), (9, -3), (9, 3), (-9, -6), (-9, 6), (-6, -9), (-6, 9), (0, -12), (0, 12), (6, -9), (6, 9),
   (9, -6), (9, 6), (-9, -9), (-9, 9), (-3, -12), (-3, 12), (3, -12), (3, 12), (9, -9), (9, 9), (-9, -12),
   (-9, 12), (-6, -12), (-6, 12), (0, -15), (0, 15), (6, -12), (6, 12), (9, -12), (9, 12), (-6, -15),
   (-6, 15), (-3, -15), (-3, 15), (3, -15), (3, 15), (6, -15), (6, 15), (-9, -15), (-9, 15), (9, -15),
   (9, 15)]

/-- The test of `v` for `ℓ = [a, b, c]`: `ℓ - 2 v vᵀ` satisfies the hypotheses of `rep_shift`. -/
def vok (a b c : ℤ) (v : ℤ × ℤ) : Bool :=
  decide (0 < a - 2 * v.1 ^ 2 ∧
    0 < (a - 2 * v.1 ^ 2) * (c - 2 * v.2 ^ 2) - (b - 2 * v.1 * v.2) * (b - 2 * v.1 * v.2) ∧
    (a - 2 * v.1 ^ 2) % 2 = 0 ∧ (b - 2 * v.1 * v.2) % 2 = 1 ∧ (c - 2 * v.2 ^ 2) % 2 = 0 ∧
    ((a - 2 * v.1 ^ 2) * (c - 2 * v.2 ^ 2) - (b - 2 * v.1 * v.2) * (b - 2 * v.1 * v.2)) % 3 = 1 ∧
    6 ^ 20 % Nat.gcd (a - 2 * v.1 ^ 2).natAbs (Nat.gcd (b - 2 * v.1 * v.2).natAbs (c - 2 * v.2 ^ 2).natAbs) = 0)

/-- The small reduced doubly hard binaries. -/
def smallCond (a b c : ℕ) : Bool :=
  a % 2 == 0 && b % 2 == 1 && c % 2 == 0 && 2 * b ≤ a && a ≤ c && (a * c - b * b) % 3 == 1 &&
    a * c - b * b ≤ 72 * a

/-- The finite check, over `a = 2a'`, `b = 2b' + 1`, `c = 2c'`. -/
def smallAll : Bool :=
  (List.range 37).all fun a' => (List.range 19).all fun b' => (List.range 46).all fun c' =>
    !smallCond (2 * a') (2 * b' + 1) (2 * c') || (a' == 5 && b' == 2 && c' == 10) ||
      vbox.any (vok ((2 * a' : ℕ) : ℤ) ((2 * b' + 1 : ℕ) : ℤ) ((2 * c' : ℕ) : ℤ))

theorem smallAll_eq : smallAll = true := by decide +kernel

theorem small_ok (a b c : ℕ) (hc : smallCond a b c = true) (ha : a ≤ 72) (hc' : c ≤ 90) :
    (a = 10 ∧ b = 5 ∧ c = 20) ∨ vbox.any (vok a b c) = true := by
  have hs := hc
  simp only [smallCond, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩ := hs
  have h := smallAll_eq
  simp only [smallAll, List.all_eq_true, List.mem_range] at h
  have key := h (a / 2) (by omega) (b / 2) (by omega) (c / 2) (by omega)
  rw [show 2 * (a / 2) = a by omega, show 2 * (b / 2) + 1 = b by omega, show 2 * (c / 2) = c by omega, hc]
    at key
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at key
  rcases key with ⟨⟨h5, h6⟩, h7⟩ | hv
  · left; omega
  · right; exact hv

/-- A representation of `[10, 5, 20]` by `hostForm 2 2 (-1) 2`. -/
def rep10 : Matrix (Fin 5) (Fin 2) ℤ := !![-2, -3; -2, 1; 0, -2; -1, -1; -1, 0]

theorem rep10_spec : rep10ᵀ * M22 * rep10 = !![10, 5; 5, 20] := by decide

theorem rep_det_le_72a (a b c : ℤ) (hb0 : 0 ≤ 2 * b) (hba : 2 * b ≤ a) (hac : a ≤ c) (ha2 : a % 2 = 0)
    (hb2 : b % 2 = 1) (hc2 : c % 2 = 0) (h3 : (a * c - b * b) % 3 = 1) (ha : a ≤ 72)
    (hd : a * c - b * b ≤ 72 * a) :
    ∃ Y : Matrix (Fin 3 ⊕ Fin 2) (Fin 2) ℤ, Yᵀ * kko112.gram * Y = !![a, b; b, c] := by
  have ha0 : 0 < a := by omega
  have hc : c ≤ 90 := by
    by_contra hc
    have : 4 * (b * b) ≤ a * a := by nlinarith
    nlinarith
  lift a to ℕ using ha0.le
  lift b to ℕ using (by omega)
  lift c to ℕ using (by omega)
  have hbb : (b : ℤ) * b ≤ a * c := by
    have : (2 * b : ℤ) * (2 * b) ≤ a * a := by nlinarith
    nlinarith
  have hbb' : b * b ≤ a * c := by exact_mod_cast hbb
  have hcond : smallCond a b c = true := by
    simp only [smallCond, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    have e : ((a * c - b * b : ℕ) : ℤ) = (a : ℤ) * c - b * b := by push_cast [Nat.cast_sub hbb']; ring
    refine ⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, ?_⟩, ?_⟩
    · have : ((a * c - b * b : ℕ) : ℤ) % 3 = 1 := by rw [e]; exact h3
      omega
    · have : ((a * c - b * b : ℕ) : ℤ) ≤ 72 * a := by rw [e]; exact hd
      omega
  rcases small_ok a b c hcond (by omega) (by omega) with ⟨rfl, rfl, rfl⟩ | hv
  · refine ⟨embedMat Local.hostBasisK3 * rep10, ?_⟩
    have e : (embedMat Local.hostBasisK3 * rep10)ᵀ * kko112.gram * (embedMat Local.hostBasisK3 * rep10) =
        rep10ᵀ * ((embedMat Local.hostBasisK3)ᵀ * kko112.gram * embedMat Local.hostBasisK3) * rep10 := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, kko112_embed, rep10_spec]
    norm_num
  · obtain ⟨v, -, hv⟩ := List.any_eq_true.mp hv
    simp only [vok, decide_eq_true_eq] at hv
    obtain ⟨h1, h2, h3', h4, h5, h6, h7⟩ := hv
    obtain ⟨Y, hY⟩ := rep_shift _ _ _ v.1 v.2 h1 h2 h3' h4 h5 h6 (prim_of_gcd _ _ _ h7)
    refine ⟨Y, hY.trans ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ### Reduction -/

/-- **Reduced doubly hard binaries.** -/
theorem rep_reduced (a b c : ℤ) (hb0 : 0 ≤ 2 * b) (hba : 2 * b ≤ a) (hac : a ≤ c) (ha2 : a % 2 = 0)
    (hb2 : b % 2 = 1) (hc2 : c % 2 = 0) (h3 : (a * c - b * b) % 3 = 1) :
    ∃ Y : Matrix (Fin 3 ⊕ Fin 2) (Fin 2) ℤ, Yᵀ * kko112.gram * Y = !![a, b; b, c] := by
  by_cases ha : 72 < a
  · exact rep_a_gt_72 a b c hb0 hba hac ha2 hb2 hc2 h3 ha
  · by_cases hd : 72 * a < a * c - b * b
    · exact rep_det_gt_72a a b c hb0 hba ha2 hb2 hc2 h3 (by omega) hd
    · exact rep_det_le_72a a b c hb0 hba hac ha2 hb2 hc2 h3 (by omega) (by omega)

/-- A vector of minimal norm. -/
theorem exists_min_vec (S : GramLattice (Fin 2)) : ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ ∀ w, w ≠ 0 → S.qf v ≤ S.qf w := by
  classical
  have hex : ∃ n : ℕ, ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ S.qf v = n := by
    refine ⟨(S.qf (Pi.single 0 1)).toNat, Pi.single 0 1, fun h => by simpa using congrFun h 0, ?_⟩
    have := S.qf_pos (v := Pi.single 0 1) (fun h => by simpa using congrFun h 0)
    omega
  obtain ⟨v, hv0, hv⟩ := Nat.find_spec hex
  refine ⟨v, hv0, fun w hw => ?_⟩
  have hpos := S.qf_pos hw
  have := Nat.find_min' hex (m := (S.qf w).toNat) ⟨w, hw, by omega⟩
  rw [hv]; omega

/-- **Kim–Kim–Oh, §4: doubly hard binaries.** `K₂₂` represents every positive binary with even
diagonal, odd off-diagonal entry and determinant `≡ 1 (mod 3)`. -/
theorem kko112_represents_hard (S : GramLattice (Fin 2)) (h00 : S.gram 0 0 % 2 = 0) (h11 : S.gram 1 1 % 2 = 0)
    (h01 : S.gram 0 1 % 2 = 1) (h3 : S.gram.det % 3 = 1) : kko112.Represents S := by
  obtain ⟨v, hv0, hmin⟩ := exists_min_vec S
  obtain ⟨b, c, N, hb0, hba, hac, hN, hiso⟩ := exists_reduced_binary S v hv0 rfl hmin
  obtain ⟨X, hX, Y, hXY⟩ := hiso
  have hs : S.gram 1 0 = S.gram 0 1 := S.gram_comm 1 0
  -- the norms of `S` are even
  have heven : ∀ x : Fin 2 → ℤ, (x ⬝ᵥ (S.gram *ᵥ x)) % 2 = 0 := by
    intro x
    have e : x ⬝ᵥ (S.gram *ᵥ x) = S.gram 0 0 * x 0 ^ 2 + 2 * (S.gram 0 1 * x 0 * x 1) + S.gram 1 1 * x 1 ^ 2 := by
      simp [dotProduct, mulVec, Fin.sum_univ_two, hs]; ring
    rw [e]
    obtain ⟨p, hp⟩ : (2 : ℤ) ∣ S.gram 0 0 := Int.dvd_of_emod_eq_zero h00
    obtain ⟨q, hq⟩ : (2 : ℤ) ∣ S.gram 1 1 := Int.dvd_of_emod_eq_zero h11
    rw [hp, hq]
    have : 2 * p * x 0 ^ 2 + 2 * (S.gram 0 1 * x 0 * x 1) + 2 * q * x 1 ^ 2 =
        2 * (p * x 0 ^ 2 + S.gram 0 1 * x 0 * x 1 + q * x 1 ^ 2) := by ring
    rw [this]; simp
  have hentry : ∀ i j, N.gram i j = (Xᵀ * S.gram * X) i j := fun i j => by rw [hX]
  have hcol : ∀ j, (Xᵀ * S.gram * X) j j = (fun i => X i j) ⬝ᵥ (S.gram *ᵥ fun i => X i j) := by
    intro j; simp [Matrix.mul_apply, dotProduct, mulVec, Fin.sum_univ_two]; ring
  have e00 : N.gram 0 0 = S.qf v := by rw [hN]; rfl
  have e11 : N.gram 1 1 = c := by rw [hN]; rfl
  have ha2 : S.qf v % 2 = 0 := by rw [← e00, hentry, hcol]; exact heven _
  have hc2 : c % 2 = 0 := by rw [← e11, hentry, hcol]; exact heven _
  -- the determinant is preserved
  have hdet : N.gram.det = S.gram.det := by
    have hdX : X.det * Y.det = 1 := by rw [← det_mul, hXY, det_one]
    have hdX2 : X.det ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdX with h | h <;> rw [h] <;> norm_num
    rw [← hX, det_mul, det_mul, det_transpose]
    linear_combination S.gram.det * hdX2
  rw [hN, det_fin_two_of] at hdet
  have hdS : S.gram.det = S.gram 0 0 * S.gram 1 1 - S.gram 0 1 * S.gram 0 1 := by rw [det_fin_two, hs]
  have hb2 : b % 2 = 1 := by
    have h1 : (S.qf v * c - b * b) % 2 = 1 := by
      rw [hdet, hdS]
      obtain ⟨p, hp⟩ : (2 : ℤ) ∣ S.gram 0 0 := Int.dvd_of_emod_eq_zero h00
      obtain ⟨r, hr⟩ : ∃ r, S.gram 0 1 = 2 * r + 1 := ⟨S.gram 0 1 / 2, by omega⟩
      rw [hp, hr]
      have : 2 * p * S.gram 1 1 - (2 * r + 1) * (2 * r + 1) = 2 * (p * S.gram 1 1 - 2 * r * r - 2 * r - 1) + 1 := by
        ring
      rw [this]
      generalize p * S.gram 1 1 - 2 * r * r - 2 * r - 1 = K
      omega
    rcases Int.emod_two_eq_zero_or_one b with h | h
    · exfalso
      obtain ⟨p, hp⟩ : (2 : ℤ) ∣ S.qf v := Int.dvd_of_emod_eq_zero ha2
      obtain ⟨q, hq⟩ : (2 : ℤ) ∣ b := Int.dvd_of_emod_eq_zero h
      rw [hp, hq] at h1
      have : 2 * p * c - 2 * q * (2 * q) = 2 * (p * c - 2 * q * q) := by ring
      rw [this] at h1
      generalize p * c - 2 * q * q = K at h1
      omega
    · exact h
  have h3' : (S.qf v * c - b * b) % 3 = 1 := by rw [hdet]; exact h3
  obtain ⟨Z, hZ⟩ := rep_reduced (S.qf v) b c hb0 hba hac ha2 hb2 hc2 h3'
  have hNS : N.Represents S := (Isometric.symm ⟨X, hX, Y, hXY⟩).represents
  exact GramLattice.Represents.trans ⟨Z, by rw [hZ, hN]⟩ hNS

end KimKimOh.Kko112

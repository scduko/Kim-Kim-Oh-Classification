import KimKimOh.PassCheck
import KimKimOh.Enum
import KimKimOh.Compute.Terminal

/-!
# The last-column test: classes, tables and options (`sec:finite`)

In the manuscript's notation the last column is `(r₁, r₂, f) = (d, e, f)`, the test at 2 is
membership in `ℛ_{j,2}` and the test at 3 is membership in `𝒰_{j,3}(σ)`; at 3 a class is
covered when a common `k` works for every maximal class `σ` extending it (`app:bounded`).

The class of a ternary `g` is `classIdx g = 128 κ + ρ₂` with `κ = 9 (d mod 3) + 3 (e mod 3) +
(f mod 3)` and `ρ₂ = loc2 (d mod 4, e mod 4, f mod 8)`. A maximal ternary with leading block
`(a, b, c)` has its class in the domain of the block (`classIdx_mem_domain`), given the checked
tables `r2` and `mx`. An option that passes `optOK` and covers the class of `S` at a threshold
`T ≤ det S` gives a representation of `S` (`rep_of_optCover`), through the general block lemma
`block_rep_core`.
-/

namespace KimKimOh

open GramLattice Tables

/-! ### Bits -/

theorem testBit_and_full128 (x i : ℕ) : (x &&& full128).testBit i = (x.testBit i && decide (i < 128)) := by
  rw [Nat.testBit_and, full128, Nat.testBit_two_pow_sub_one]

theorem pairProd_testBit {rows cols κ ρ : ℕ} (hκ : κ < 27) (hρ : ρ < 128) :
    (pairProd rows cols).testBit (128 * κ + ρ) = true ↔
      cols.testBit κ = true ∧ rows.testBit ρ = true := by
  unfold pairProd
  rw [natFoldOr_testBit]
  constructor
  · rintro ⟨κ', hκ', h⟩
    cases hc : cols.testBit κ' with
    | false => simp [hc] at h
    | true =>
      simp only [hc, Bool.cond_true, Nat.testBit_shiftLeft, testBit_and_full128, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have e : κ' = κ := by omega
      subst e
      exact ⟨hc, by rwa [show 128 * κ' + ρ - 128 * κ' = ρ by omega] at h2⟩
  · rintro ⟨hc, hr⟩
    refine ⟨κ, hκ, ?_⟩
    simp only [hc, Bool.cond_true, Nat.testBit_shiftLeft, testBit_and_full128, Bool.and_eq_true,
      decide_eq_true_eq, show 128 * κ + ρ - 128 * κ = ρ by omega]
    exact ⟨by omega, hr, hρ⟩

/-! ### Column classes at 3 -/

theorem liftMask3_testBit {d e f : ℕ} (hd : d < 9) (he : e < 9) (hf : f < 9) :
    (liftMask3 (9 * (d % 3) + 3 * (e % 3) + f % 3)).testBit (loc3 d e f) = true := by
  unfold liftMask3
  rw [natFoldOr_testBit]
  refine ⟨9 * (d / 3) + 3 * (e / 3) + f / 3, by omega, ?_⟩
  have e1 : (9 * (d % 3) + 3 * (e % 3) + f % 3) / 9 + 3 * ((9 * (d / 3) + 3 * (e / 3) + f / 3) / 9)
      = d := by omega
  have e2 : (9 * (d % 3) + 3 * (e % 3) + f % 3) / 3 % 3 +
      3 * ((9 * (d / 3) + 3 * (e / 3) + f / 3) / 3 % 3) = e := by omega
  have e3 : (9 * (d % 3) + 3 * (e % 3) + f % 3) % 3 + 3 * ((9 * (d / 3) + 3 * (e / 3) + f / 3) % 3)
      = f := by omega
  rw [e1, e2, e3, testBit_one_shiftLeft, decide_eq_true_eq]

theorem colsIn_spec {maxm set κ l : ℕ} (h : (colsIn maxm set).testBit κ = true)
    (hl : (liftMask3 κ).testBit l = true) (hm : maxm.testBit l = true) : set.testBit l = true := by
  unfold colsIn at h
  rw [natFoldOr_testBit] at h
  obtain ⟨κ', -, h⟩ := h
  cases heq : Nat.beq (liftMask3 κ' &&& maxm &&& set) (liftMask3 κ' &&& maxm) with
  | false => simp [heq] at h
  | true =>
    simp only [heq, Bool.cond_true, testBit_one_shiftLeft, decide_eq_true_eq] at h
    subst h
    have := congrArg (fun n => n.testBit l) (Nat.eq_of_beq_eq_true heq)
    simpa [Nat.testBit_and, hl, hm] using this

theorem colsMax_spec {maxm κ l : ℕ} (hκ : κ < 27) (hl : (liftMask3 κ).testBit l = true)
    (hm : maxm.testBit l = true) : (colsMax maxm).testBit κ = true := by
  unfold colsMax
  rw [natFoldOr_testBit]
  refine ⟨κ, hκ, ?_⟩
  have hne : Nat.beq (liftMask3 κ &&& maxm) 0 = false := by
    refine beq_false_of_ne fun h0 => ?_
    have := congrArg (fun n => n.testBit l) h0
    simp [Nat.testBit_and, hl, hm] at this
  simp only [hne, Bool.cond_false, testBit_one_shiftLeft, decide_true]

/-! ### The tables -/

theorem rows2_testBit {blk l : ℕ} (hl : l < 128)
    (h : det4 (blk / 32) (blk / 8 % 4) (blk % 8) (l / 32) (l / 8 % 4) (l % 8) ≠ 0) :
    (rows2 blk).testBit l = true := by
  unfold rows2
  rw [natFoldOr_testBit]
  refine ⟨l, hl, ?_⟩
  have hne : Nat.beq (det4 (blk / 32) (blk / 8 % 4) (blk % 8) (l / 32) (l / 8 % 4) (l % 8)) 0 =
      false := beq_false_of_ne h
  simp only [hne, Bool.cond_false, testBit_one_shiftLeft, decide_true]

theorem r2_get {r2 : ℕ} (h : r2OK r2 = true) {blk : ℕ} (hb : blk < 256) :
    tget r2 128 blk = rows2 blk :=
  Nat.eq_of_beq_eq_true (natAllR_spec h blk hb)

theorem zsMask_elem : ∀ e < 32, zsMask.testBit e = true → zs3.elem (e / 9, e / 3 % 3, e % 3) = true := by
  decide

theorem zsMask_spec {e : ℕ} (he : e < 32) (h : zsMask.testBit e = true) :
    (e / 9, e / 3 % 3, e % 3) ∈ zs3 :=
  List.elem_iff.mp (zsMask_elem e he h)

theorem tget_lt (tab w blk : ℕ) : tget tab w blk < 2 ^ w := by
  unfold tget
  exact lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)

/-- **The maximal residues at 3**: the residue of a maximal ternary is marked in `mx`. -/
theorem mx_spec {mx mw : ℕ}
    (h : ∀ blk < 729, mxRowOK (tget mx 729 blk) (tget mw 3645 blk) blk = true) (g : Tern)
    (hmax : IsMaximal g.toMatrix) :
    (tget mx 729 (chunk3 g)).testBit (loc3 (r9 g.d) (r9 g.e) (r9 g.f)) = true := by
  have ha := r9_lt g.a; have hb := r9_lt g.b; have hc := r9_lt g.c
  have hd := r9_lt g.d; have he := r9_lt g.e; have hf := r9_lt g.f
  set blk := chunk3 g with hblk
  set l := loc3 (r9 g.d) (r9 g.e) (r9 g.f) with hl
  obtain ⟨hblk', e1, e2, e3⟩ : blk < 729 ∧ blk / 81 = r9 g.a ∧ blk / 9 % 9 = r9 g.b ∧
      blk % 9 = r9 g.c := digits9 ha hb hc
  obtain ⟨hl', f1, f2, f3⟩ : l < 729 ∧ l / 81 = r9 g.d ∧ l / 9 % 9 = r9 g.e ∧
      l % 9 = r9 g.f := digits9 hd he hf
  have hrow := natAllR_spec (h blk hblk') l hl'
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hrow
  rcases hrow with hrow | ⟨hz, hiso⟩
  · exact hrow
  · exfalso
    set code := tget (tget mw 3645 blk) 5 l
    have hcode : code < 32 := tget_lt _ _ _
    have hmem := zsMask_spec hcode hz
    have hn := nonmax3_false g hmax
    rw [e1, e2, e3, f1, f2, f3] at hiso
    have : nonmax3 (r9 g.a) (r9 g.b) (r9 g.c) (r9 g.d) (r9 g.e) (r9 g.f) = true :=
      List.any_eq_true.mpr ⟨_, hmem, hiso⟩
    rw [hn] at this
    exact Bool.false_ne_true this

theorem mx_all {mx mw : ℕ} (h : ∀ i < 9, mxRange mx mw (81 * i) 81 = true) :
    ∀ blk < 729, mxRowOK (tget mx 729 blk) (tget mw 3645 blk) blk = true := by
  intro blk hblk
  have := natAllR_spec (h (blk / 81) (by omega)) (blk % 81) (Nat.mod_lt _ (by norm_num))
  rwa [show 81 * (blk / 81) + blk % 81 = blk by omega] at this

/-! ### The class of a ternary and the domain -/

/-- The last-column class `128 κ + ρ₂` of a ternary. -/
def classIdx (g : Tern) : ℕ :=
  128 * (9 * rp 3 g.d + 3 * rp 3 g.e + rp 3 g.f) + loc2 (r4 g.d) (r4 g.e) (r8 g.f)

theorem kappa_lt (g : Tern) : 9 * rp 3 g.d + 3 * rp 3 g.e + rp 3 g.f < 27 := by
  have h1 := rp_lt (show 0 < 3 by norm_num) g.d
  have h2 := rp_lt (show 0 < 3 by norm_num) g.e
  have h3 := rp_lt (show 0 < 3 by norm_num) g.f
  omega

theorem loc2_lt (g : Tern) : loc2 (r4 g.d) (r4 g.e) (r8 g.f) < 128 := by
  have := r4_lt g.d; have := r4_lt g.e; have := r8_lt g.f
  unfold loc2; omega

/-- The lift of the class of `g` modulo 9. -/
theorem liftMask3_class (g : Tern) :
    (liftMask3 (9 * rp 3 g.d + 3 * rp 3 g.e + rp 3 g.f)).testBit
      (loc3 (r9 g.d) (r9 g.e) (r9 g.f)) = true := by
  rw [← r9_mod_three g.d, ← r9_mod_three g.e, ← r9_mod_three g.f]
  exact liftMask3_testBit (r9_lt _) (r9_lt _) (r9_lt _)

/-- **The class of a maximal ternary lies in the domain of its block.** -/
theorem classIdx_mem_domain {r2 : ℕ} (hr2 : r2OK r2 = true) {maxm : ℕ} (g : Tern)
    (hmax : IsMaximal g.toMatrix) {a b c : ℕ} (ha : g.a = a) (hb : g.b = b) (hc : g.c = c)
    (hm : maxm.testBit (loc3 (r9 g.d) (r9 g.e) (r9 g.f)) = true) :
    (domainB r2 maxm a b c).testBit (classIdx g) = true := by
  unfold domainB classIdx
  rw [pairProd_testBit (kappa_lt g) (loc2_lt g)]
  refine ⟨colsMax_spec (kappa_lt g) (liftMask3_class g) hm, ?_⟩
  have hblk : blk2 (a % 8) (b % 4) (c % 8) < 256 := by unfold blk2; omega
  rw [r2_get hr2 hblk]
  have hd := r4_lt g.d; have he := r4_lt g.e; have hf := r8_lt g.f
  refine rows2_testBit (loc2_lt g) ?_
  have e1 : blk2 (a % 8) (b % 4) (c % 8) / 32 = r8 g.a := by rw [ha, r8_natCast]; unfold blk2; omega
  have e2 : blk2 (a % 8) (b % 4) (c % 8) / 8 % 4 = r4 g.b := by
    rw [hb, r4_natCast]; unfold blk2; omega
  have e3 : blk2 (a % 8) (b % 4) (c % 8) % 8 = r8 g.c := by rw [hc, r8_natCast]; unfold blk2; omega
  have f1 : loc2 (r4 g.d) (r4 g.e) (r8 g.f) / 32 = r4 g.d := by unfold loc2; omega
  have f2 : loc2 (r4 g.d) (r4 g.e) (r8 g.f) / 8 % 4 = r4 g.e := by unfold loc2; omega
  have f3 : loc2 (r4 g.d) (r4 g.e) (r8 g.f) % 8 = r8 g.f := by unfold loc2; omega
  rw [e1, e2, e3, f1, f2, f3]
  exact det4_ne_zero g hmax

/-! ### Stripping primes and trial division -/

theorem stripF_succ (p k m : ℕ) :
    stripF p (k + 1) m = cond (Nat.beq (m % p) 0) (stripF p k (m / p)) m := rfl

theorem stripF_spec (p : ℕ) : ∀ k m : ℕ, ∃ i, m = stripF p k m * p ^ i := by
  intro k
  induction k with
  | zero => intro m; exact ⟨0, by simp [stripF]⟩
  | succ k ih =>
    intro m
    rw [stripF_succ]
    cases h : Nat.beq (m % p) 0 with
    | false => exact ⟨0, by simp⟩
    | true =>
      obtain ⟨i, hi⟩ := ih (m / p)
      refine ⟨i + 1, ?_⟩
      have hm : p ∣ m := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h)
      simp only [Bool.cond_true]
      calc m = p * (m / p) := (Nat.mul_div_cancel' hm).symm
        _ = stripF p k (m / p) * p ^ (i + 1) := by rw [pow_succ]; nth_rewrite 1 [hi]; ring

theorem dvd_stripF {p q : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) (k : ℕ) {m : ℕ} (hm : p ∣ m) :
    p ∣ stripF q k m := by
  obtain ⟨i, hi⟩ := stripF_spec q k m
  rw [hi] at hm
  rcases (Nat.Prime.dvd_mul hp).mp hm with h | h
  · exact h
  · exact absurd (hp.dvd_of_dvd_pow h) hq

/-- **Stripping**: if `2`, `3` and the entries of `F` strip `n` to 1, every prime `p ≥ 5`
dividing `n` divides an entry of `F`. -/
theorem stripL_cover {α : Type} {q : α → ℕ} {F : List α} {n : ℕ} (h : stripL q F n = 1) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hpn : p ∣ n) : ∃ e ∈ F, p ∣ q e := by
  by_contra hne
  push Not at hne
  have h2 : ¬ p ∣ 2 := fun h' => by have := Nat.le_of_dvd (by norm_num) h'; omega
  have h3 : ¬ p ∣ 3 := fun h' => by have := Nat.le_of_dvd (by norm_num) h'; omega
  have key : ∀ F' : List α, (∀ e ∈ F', ¬ p ∣ q e) → p ∣ stripL q F' n := by
    intro F' hF'
    induction F' with
    | nil => exact dvd_stripF hp h3 64 (dvd_stripF hp h2 64 hpn)
    | cons e F' ih =>
      exact dvd_stripF hp (hF' e List.mem_cons_self) 64
        (ih fun q' hq' => hF' q' (List.mem_cons_of_mem _ hq'))
  have := key F hne
  rw [h] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem isPrimeTD_spec {p r : ℕ} (h : isPrimeTD p r = true) : p.Prime := by
  unfold isPrimeTD at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  by_contra hp
  have hm := Nat.minFac_sq_le_self (by omega) hp
  have hm2 : 2 ≤ p.minFac := (Nat.minFac_prime (by omega)).two_le
  have hlt : p.minFac < r + 2 := by
    by_contra hc
    push Not at hc
    have : (r + 2) * (r + 2) ≤ p.minFac ^ 2 := by nlinarith
    omega
  have hi := natAllR_spec h3 (p.minFac - 2) (by omega)
  rw [show p.minFac - 2 + 2 = p.minFac by omega, Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd p)] at hi
  exact absurd hi (by decide)

/-! ### The checks of an option -/

theorem bAbs_sq (s b x y : ℕ) (yneg : Bool) :
    ((bAbs s b x y yneg : ℕ) : ℤ) ^ 2 = ((b : ℤ) - s * x * dirY (x, y, yneg)) ^ 2 := by
  unfold bAbs dirY
  cases yneg with
  | true =>
    show ((b + s * x * y : ℕ) : ℤ) ^ 2 = ((b : ℤ) - s * x * (-(y : ℤ))) ^ 2
    push_cast; ring
  | false =>
    show ((cond (Nat.ble (s * x * y) b) (b - s * x * y) (s * x * y - b) : ℕ) : ℤ) ^ 2 =
      ((b : ℤ) - s * x * (y : ℤ)) ^ 2
    cases hle : Nat.ble (s * x * y) b with
    | true =>
      have h := Nat.ble_eq.mp hle
      simp only [Bool.cond_true]; push_cast [h]; ring
    | false =>
      have h : b < s * x * y := by
        by_contra h'; push Not at h'; rw [Nat.ble_eq.mpr h'] at hle; exact absurd hle (by decide)
      simp only [Bool.cond_false]; push_cast [h.le]; ring

theorem dirY_sq (x y : ℕ) (yneg : Bool) : dirY (x, y, yneg) * dirY (x, y, yneg) = (y : ℤ) * y := by
  unfold dirY; cases yneg <;> simp

/-- `Δ` of an option is `corrDelta`. -/
theorem deltaO_eq (g : Tern) {s a b c x y : ℕ} {yneg : Bool} (ha : g.a = a) (hb : g.b = b)
    (hc : g.c = c) (hxa : s * x * x < a) (hyc : s * y * y < c)
    (hbb : bAbs s b x y yneg * bAbs s b x y yneg < (a - s * x * x) * (c - s * y * y)) :
    ((deltaO s a b c x y yneg : ℕ) : ℤ) = g.corrDelta s x (dirY (x, y, yneg)) := by
  unfold deltaO
  have h2 := bAbs_sq s b x y yneg
  have hy2 := dirY_sq x y yneg
  rw [Nat.cast_sub hbb.le]
  push_cast [hxa.le, hyc.le]
  rw [Tern.corrDelta, Tern.delta, ha, hb, hc]
  have : ((bAbs s b x y yneg : ℕ) : ℤ) * (bAbs s b x y yneg : ℕ) =
      ((b : ℤ) - s * x * dirY (x, y, yneg)) ^ 2 := by rw [← h2]; ring
  rw [this]
  linear_combination ((a : ℤ) * s - s * s * x * x) * hy2

theorem keptSum_eq (δ cnt G : ℕ) : ∀ F : List FactorEntry, keptSum δ cnt G F =
    (((F.filter (fun q => q.kind = 0)).map (·.q)).map
      fun p => wtN δ cnt p * ((G + p - 1) / p)).sum
  | [] => rfl
  | q :: F => by
    have ih := keptSum_eq δ cnt G F
    show cond (Nat.beq q.kind 0) _ 0 + keptSum δ cnt G F = _
    rw [ih]
    by_cases h : q.kind = 0
    · rw [show Nat.beq q.kind 0 = true from Nat.beq_eq_true_eq _ _ ▸ h, Bool.cond_true]
      simp [h]
    · rw [beq_false_of_ne h, Bool.cond_false]
      simp [h]

/-- The facts of `block_rep_core` provided by `optOK`. -/
theorem optOK_facts (H : HostSpec) (S : GramLattice (Fin 3)) {a b c : ℕ}
    (ha : (ternOf S).a = a) (hb : (ternOf S).b = b) (hc : (ternOf S).c = c)
    {x y G : ℕ} {yneg : Bool} {F : List FactorEntry}
    (hopt : optOK H.j H.s a b c ⟨x, y, yneg, G, F⟩ = true) :
    0 < G ∧ (ternOf S).corrDelta H.s x (dirY (x, y, yneg)) = (deltaO H.s a b c x y yneg : ℤ) ∧
    ∃ Om : Finset ℕ, (∀ p ∈ Om, ∀ k : ℤ,
        ((ternOf S).corr H.s x (dirY (x, y, yneg)) k).OkAt H.j p) ∧
      (∀ p ∈ bigPrimesOf ((ternOf S).corrDelta H.s x (dirY (x, y, yneg))), p ∉ Om →
        ¬ ((p : ℤ) ∣ (ternOf S).a ∧ (p : ℤ) ∣ (ternOf S).b ∧ (p : ℤ) ∣ (ternOf S).c ∧
          (p : ℤ) ∣ (x : ℤ) ∧ (p : ℤ) ∣ dirY (x, y, yneg))) ∧
      ∑ p ∈ bigPrimesOf ((ternOf S).corrDelta H.s x (dirY (x, y, yneg))) \ Om,
        (ternOf S).weight p * ((G + p - 1) / p) < G := by
  classical
  set g := ternOf S with hg
  simp only [optOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hopt
  obtain ⟨⟨⟨⟨⟨⟨hxa, hyc⟩, hbb⟩, hstrip⟩, hent⟩, hG⟩, hsumN⟩ := hopt
  have hΔ := deltaO_eq g ha hb hc hxa hyc hbb
  set Δ := deltaO H.s a b c x y yneg with hΔdef
  have hstrip' : stripL FactorEntry.q F Δ = 1 := Nat.eq_of_beq_eq_true hstrip
  have hent' : ∀ q ∈ F, entryOK H.j H.s a b c x y q = true := allR_spec hent
  refine ⟨hG, hΔ.symm, ?_⟩
  have hΔpos : 0 < Δ := Nat.sub_pos_of_lt hbb
  have hΔZ : g.corrDelta H.s x (dirY (x, y, yneg)) ≠ 0 := by rw [← hΔ]; exact_mod_cast hΔpos.ne'
  have hcov : ∀ p ∈ bigPrimesOf (g.corrDelta H.s x (dirY (x, y, yneg))), ∃ q ∈ F, p ∣ q.q := by
    intro p hp
    obtain ⟨hpp, h5, hdvd⟩ := (mem_bigPrimesOf hΔZ).mp hp
    rw [← hΔ] at hdvd
    exact stripL_cover hstrip' hpp h5 (Int.natCast_dvd_natCast.mp hdvd)
  -- the kept entries are primes
  have hkept : ∀ p ∈ bigPrimesOf (g.corrDelta H.s x (dirY (x, y, yneg))), (¬ ∃ q ∈ F, q.kind ≠ 0 ∧ p ∣ q.q) →
      ∃ q ∈ F, q.kind = 0 ∧ q.q = p := by
    intro p hp hnot
    obtain ⟨hpp, -, -⟩ := (mem_bigPrimesOf hΔZ).mp hp
    obtain ⟨q, hqF, hpq⟩ := hcov p hp
    have htag : q.kind = 0 := by by_contra h'; exact hnot ⟨q, hqF, h', hpq⟩
    have he := hent' q hqF
    unfold entryOK at he
    rw [show Nat.beq q.kind 0 = true from Nat.beq_eq_true_eq _ _ ▸ htag, Bool.cond_true,
      Bool.and_eq_true] at he
    have hq := isPrimeTD_spec he.1
    exact ⟨q, hqF, htag, ((Nat.prime_dvd_prime_iff_eq hpp hq).mp hpq).symm⟩
  let Om : Finset ℕ :=
    (bigPrimesOf (g.corrDelta H.s x (dirY (x, y, yneg)))).filter (fun p => ∃ q ∈ F, q.kind ≠ 0 ∧ p ∣ q.q)
  refine ⟨Om, ?_, ?_, ?_⟩
  · -- the omitted primes: a diagonal entry of `B'` in the square class of `j`
    intro p hp k
    obtain ⟨hpb, q, hqF, htag, hpq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpp, -, -⟩ := (mem_bigPrimesOf hΔZ).mp hpb
    have he := hent' q hqF
    unfold entryOK at he
    rw [beq_false_of_ne htag, Bool.cond_false, Bool.and_eq_true] at he
    have hgcd := Nat.eq_of_beq_eq_true he.1
    have hdiag := Nat.modEq_iff_dvd.mp (Nat.eq_of_beq_eq_true he.2)
    have hdiagp : (p : ℤ) ∣ ((H.j * q.w * q.w : ℕ) : ℤ) - (diagO H.s a c x y q.kind : ℕ) :=
      (Int.natCast_dvd_natCast.mpr hpq).trans hdiag
    right
    refine ⟨q.w, fun hw => ?_, ?_⟩
    · have : p ∣ Nat.gcd q.w q.q := Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hw) hpq
      rw [hgcd] at this
      exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
    · unfold diagO at hdiagp
      by_cases h1 : q.kind = 1
      · rw [show Nat.beq q.kind 1 = true from Nat.beq_eq_true_eq _ _ ▸ h1, Bool.cond_true] at hdiagp
        left
        rw [← dvd_neg]
        convert hdiagp using 1
        simp only [Tern.corr, ha, Nat.cast_sub hxa.le]
        push_cast; ring
      · rw [beq_false_of_ne h1, Bool.cond_false] at hdiagp
        right; left
        rw [← dvd_neg]
        convert hdiagp using 1
        simp only [Tern.corr, hc, Nat.cast_sub hyc.le]
        have := dirY_sq x y yneg
        push_cast; linear_combination (H.s : ℤ) * this
  · -- `B` and `α` do not both vanish at the kept primes
    intro p hp hpOm
    have hnot : ¬ ∃ q ∈ F, q.kind ≠ 0 ∧ p ∣ q.q := fun h' => hpOm (Finset.mem_filter.mpr ⟨hp, h'⟩)
    obtain ⟨q, hqF, htag, rfl⟩ := hkept _ hp hnot
    have he := hent' q hqF
    unfold entryOK at he
    rw [show Nat.beq q.kind 0 = true from Nat.beq_eq_true_eq _ _ ▸ htag, Bool.cond_true,
      Bool.and_eq_true] at he
    rintro ⟨h1, h2, h3, h4, h5⟩
    rw [ha] at h1; rw [hb] at h2; rw [hc] at h3
    have h5' : (q.q : ℤ) ∣ (y : ℤ) := by
      have : dirY (x, y, yneg) = y ∨ dirY (x, y, yneg) = -(y : ℤ) := by
        unfold dirY; cases yneg <;> simp
      rcases this with e | e <;> rw [e] at h5
      · exact h5
      · exact (dvd_neg).mp h5
    have := he.2
    simp only [Int.natCast_dvd_natCast] at h1 h2 h3 h4 h5'
    simp [Nat.mod_eq_zero_of_dvd h1, Nat.mod_eq_zero_of_dvd h2, Nat.mod_eq_zero_of_dvd h3,
      Nat.mod_eq_zero_of_dvd h4, Nat.mod_eq_zero_of_dvd h5'] at this
  · -- the sieve sum over the kept primes
    have hδ0 := delta_pos S
    have hbc : b * b ≤ a * c := by
      have : (0 : ℤ) < (a : ℤ) * c - b * b := by
        have e : g.delta = (a : ℤ) * c - b * b := by simp only [Tern.delta, ha, hb, hc]
        rw [← e]; exact hδ0
      have : ((b * b : ℕ) : ℤ) < ((a * c : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this.le
    have hδeq : g.delta = ((a * c - b * b : ℕ) : ℤ) := by
      push_cast [hbc]; simp only [Tern.delta, ha, hb, hc]
    have hw : ∀ p, g.weight p = wtN (a * c - b * b) (Nat.gcd a (Nat.gcd b c)) p :=
      weight_eq g ha hb hc hδeq
    set f : ℕ → ℕ := fun p => wtN (a * c - b * b) (Nat.gcd a (Nat.gcd b c)) p * ((G + p - 1) / p)
    have hsub : bigPrimesOf (g.corrDelta H.s x (dirY (x, y, yneg))) \ Om ⊆
        ((F.filter (fun q => q.kind = 0)).map (·.q)).toFinset := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      have hnot : ¬ ∃ q ∈ F, q.kind ≠ 0 ∧ p ∣ q.q :=
        fun h' => hp.2 (Finset.mem_filter.mpr ⟨hp.1, h'⟩)
      obtain ⟨q, hqF, htag, rfl⟩ := hkept _ hp.1 hnot
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨q, List.mem_filter.mpr ⟨hqF, by simpa using htag⟩, rfl⟩
    calc ∑ p ∈ bigPrimesOf (g.corrDelta H.s x (dirY (x, y, yneg))) \ Om, g.weight p * ((G + p - 1) / p)
        = ∑ p ∈ bigPrimesOf (g.corrDelta H.s x (dirY (x, y, yneg))) \ Om, f p := by simp only [hw, f]
      _ ≤ ∑ p ∈ ((F.filter (fun q => q.kind = 0)).map (·.q)).toFinset, f p :=
          Finset.sum_le_sum_of_subset hsub
      _ ≤ (((F.filter (fun q => q.kind = 0)).map (·.q)).map f).sum := toFinset_sum_le f _
      _ = keptSum (a * c - b * b) (Nat.gcd a (Nat.gcd b c)) G F := (keptSum_eq _ _ _ F).symm
      _ < G := hsumN

/-! ### Coverage gives local progressions -/

theorem coverW_cases {row1 row2 row4 col1 col3 : ℕ} {lv : ℕ → Bool} {κ ρ : ℕ} (hκ : κ < 27)
    (hρ : ρ < 128)
    (h : (coverW row1 row2 row4 col1 col3 lv).testBit (128 * κ + ρ) = true) :
    (lv 1 = true ∧ row1.testBit ρ = true ∧ col1.testBit κ = true) ∨
    (lv 2 = true ∧ row2.testBit ρ = true ∧ col1.testBit κ = true) ∨
    (lv 4 = true ∧ row4.testBit ρ = true ∧ col1.testBit κ = true) ∨
    (lv 3 = true ∧ row1.testBit ρ = true ∧ col3.testBit κ = true) ∨
    (lv 6 = true ∧ row2.testBit ρ = true ∧ col3.testBit κ = true) ∨
    (lv 12 = true ∧ row4.testBit ρ = true ∧ col3.testBit κ = true) := by
  have key : ∀ (v : Bool) (r k : ℕ), (cond v (pairProd r k) 0).testBit (128 * κ + ρ) = true →
      v = true ∧ r.testBit ρ = true ∧ k.testBit κ = true := by
    intro v r k hv
    cases v with
    | false => simp at hv
    | true =>
      rw [Bool.cond_true, pairProd_testBit hκ hρ] at hv
      exact ⟨rfl, hv.2, hv.1⟩
  unfold coverW at h
  simp only [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact Or.inl (key _ _ _ h)
  · exact Or.inr (Or.inl (key _ _ _ h))
  · exact Or.inr (Or.inr (Or.inl (key _ _ _ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ _ _ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ _ _ h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key _ _ _ h)))))

/-- A row of step `w` at 2 gives a progression of accepted corrections. -/
theorem prog2_of_stepSet2 (acc : BT ℕ) (s : ℕ) (g : Tern) {a b c : ℕ} (ha : g.a = a)
    (hb : g.b = b) (hc : g.c = c) (x y : ℤ) {w : ℕ} (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (h : (stepSet2 acc s (a % 8) (b % 4) (c % 8) (r4 x) (r4 y) w).testBit
      (loc2 (r4 g.d) (r4 g.e) (r8 g.f)) = true) :
    ∃ k₀ : ℤ, ∀ k : ℤ, (w : ℤ) ∣ k - k₀ → accepted2 acc (g.corr s x y k) = true := by
  rw [← r8_natCast, ← r4_natCast, ← r8_natCast, ← ha, ← hb, ← hc] at h
  obtain ⟨k₀, hk₀, hk⟩ := stepSet2_spec h hw
  refine ⟨k₀, fun k hk' => accepted_of_fine2 acc s g x y k ?_⟩
  have hkr := r4_lt k
  refine hk _ hkr ?_
  have hw4 : (w : ℤ) ∣ 4 := by rcases hw with h | h | h <;> rw [h] <;> norm_num
  have hr : ((r4 k : ℕ) : ℤ) = k % 4 := by unfold r4; omega
  have : (w : ℤ) ∣ ((r4 k + 4 - k₀ : ℕ) : ℤ) := by
    have e : ((r4 k + 4 - k₀ : ℕ) : ℤ) = (k - k₀) + 4 * (1 - k / 4) := by
      push_cast [show k₀ ≤ r4 k + 4 by omega]; rw [hr]; have := Int.emod_add_mul_ediv k 4; linarith
    rw [e]; exact dvd_add hk' (dvd_mul_of_dvd_left hw4 _)
  exact_mod_cast this

theorem rp3_cases (k : ℤ) : rp 3 k = 0 ∨ rp 3 k = 1 ∨ rp 3 k = 2 := by
  have := rp_lt (show 0 < 3 by norm_num) k; omega

/-- A column class of step 1 at 3 accepts every correction. -/
theorem prog3_one (acc : BT ℕ) (s : ℕ) (g : Tern) {a b c maxm κ : ℕ} (ha : g.a = a)
    (hb : g.b = b) (hc : g.c = c) (x y : ℤ)
    (hκ : κ = 9 * rp 3 g.d + 3 * rp 3 g.e + rp 3 g.f)
    (hm : maxm.testBit (loc3 (r9 g.d) (r9 g.e) (r9 g.f)) = true)
    (h : (cols1 (perms3 acc s (a % 9) (b % 9) (c % 9)) maxm (rp 3 x) (rp 3 y)).testBit κ = true) :
    ∀ k : ℤ, accepted3 acc (g.corr s x y k) = true := by
  intro k
  have hl := liftMask3_class g
  rw [← hκ] at hl
  have hset := colsIn_spec h hl hm
  rw [← r9_natCast, ← r9_natCast, ← r9_natCast, ← ha, ← hb, ← hc] at hset
  simp only [Nat.testBit_and, Bool.and_eq_true] at hset
  obtain ⟨⟨h0, h1⟩, h2⟩ := hset
  refine accepted_of_get3 acc s g x y k ?_
  rcases rp3_cases k with e | e | e <;> rw [e]
  · exact h0
  · exact h1
  · exact h2

/-- A column class of step 3 at 3 accepts the corrections of a class of `k` modulo 3. -/
theorem prog3_three (acc : BT ℕ) (s : ℕ) (g : Tern) {a b c maxm κ : ℕ} (ha : g.a = a)
    (hb : g.b = b) (hc : g.c = c) (x y : ℤ)
    (hκ : κ = 9 * rp 3 g.d + 3 * rp 3 g.e + rp 3 g.f)
    (hm : maxm.testBit (loc3 (r9 g.d) (r9 g.e) (r9 g.f)) = true)
    (h : (cols3 (perms3 acc s (a % 9) (b % 9) (c % 9)) maxm (rp 3 x) (rp 3 y)).testBit κ = true) :
    ∃ k₀ : ℤ, ∀ k : ℤ, (3 : ℤ) ∣ k - k₀ → accepted3 acc (g.corr s x y k) = true := by
  have hl := liftMask3_class g
  rw [← hκ] at hl
  have main : ∀ k₀ < 3, (colsIn maxm (get3 (perms3 acc s (a % 9) (b % 9) (c % 9)) (rp 3 x) (rp 3 y)
      k₀)).testBit κ = true →
      ∃ k₀ : ℤ, ∀ k : ℤ, (3 : ℤ) ∣ k - k₀ → accepted3 acc (g.corr s x y k) = true := by
    intro k₀ hk₀ hcol
    have hset := colsIn_spec hcol hl hm
    rw [← r9_natCast, ← r9_natCast, ← r9_natCast, ← ha, ← hb, ← hc] at hset
    refine ⟨k₀, fun k hk => accepted_of_get3 acc s g x y k ?_⟩
    have e : rp 3 k = k₀ := rp_eq (by exact_mod_cast hk) hk₀
    rwa [e]
  unfold cols3 at h
  simp only [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact main 0 (by norm_num) h
  · exact main 1 (by norm_num) h
  · exact main 2 (by norm_num) h

/-! ### An option covering the class of `S` -/

/-- **An option covering the class of `S` at a threshold `T ≤ det S` gives `L ⊇ S`.** -/
theorem rep_of_optCover (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) {a b c : ℕ}
    (ha : (ternOf S).a = a) (hb : (ternOf S).b = b) (hc : (ternOf S).c = c) {maxm : ℕ}
    (hm : maxm.testBit (loc3 (r9 (ternOf S).d) (r9 (ternOf S).e) (r9 (ternOf S).f)) = true)
    (o : TermOpt) (hopt : optOK H.j H.s a b c o = true) {T : ℕ} (hT : (T : ℤ) ≤ (ternOf S).det)
    (hcov : (optCover H.acc2 H.acc3 H.s a b c maxm T o).testBit (classIdx (ternOf S)) = true) :
    L.Represents S := by
  obtain ⟨x, y, yneg, G, F⟩ := o
  set g := ternOf S with hg
  obtain ⟨hG, hΔ, Om, hOm, hBα, hsum⟩ := optOK_facts H S ha hb hc hopt
  obtain ⟨-, hdelta⟩ := delta_natCast S ha hb hc
  have hD := det_pos S
  have gen : ∀ w₂ w₃ : ℕ, (w₂ = 1 ∨ w₂ = 2 ∨ w₂ = 4) → (w₃ = 1 ∨ w₃ = 3) →
      levelOK H.s (a * c - b * b) (deltaO H.s a b c x y yneg) T (w₂ * w₃) G = true →
      (stepSet2 H.acc2 H.s (a % 8) (b % 4) (c % 8) (x % 4) (resY 4 (x, y, yneg)) w₂).testBit
        (loc2 (r4 g.d) (r4 g.e) (r8 g.f)) = true →
      (∃ k₃ : ℤ, ∀ k : ℤ, (w₃ : ℤ) ∣ k - k₃ →
        accepted3 H.acc3 (g.corr H.s x (dirY (x, y, yneg)) k) = true) →
      L.Represents S := by
    intro w₂ w₃ hw₂ hw₃ hlv hrow hcol
    rw [show x % 4 = r4 (x : ℤ) from (r4_natCast x).symm, ← r4_dirY (x, y, yneg)] at hrow
    obtain ⟨k₂, hk₂⟩ := prog2_of_stepSet2 H.acc2 H.s g ha hb hc x (dirY (x, y, yneg)) hw₂ hrow
    obtain ⟨k₃, hk₃⟩ := hcol
    refine block_rep_core H hK L hL S hmax x (dirY (x, y, yneg)) w₂ w₃ hw₂ hw₃
      ⟨k₂, fun k hk => H.acc2_sound _ (hk₂ k hk)⟩ ⟨k₃, fun k hk => H.acc3_sound _ (hk₃ k hk)⟩ Om hOm hBα G hG
      hsum ?_
    unfold levelOK at hlv
    rw [Nat.blt_eq] at hlv
    have h1 : ((H.s * (w₂ * w₃ * G) * (w₂ * w₃ * G) * ((a * c - b * b) * (a * c - b * b)) : ℕ) : ℤ) <
        ((4 * deltaO H.s a b c x y yneg * T : ℕ) : ℤ) := by exact_mod_cast hlv
    push_cast at h1
    rw [hΔ, hdelta]
    have hΔ0 : (0 : ℤ) ≤ (deltaO H.s a b c x y yneg : ℤ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hκ := kappa_lt g
  have hρ := loc2_lt g
  unfold optCover classIdx at hcov
  have hx3 : x % 3 = rp 3 (x : ℤ) := (rp_natCast 3 x).symm
  have hy3 : resY 3 (x, y, yneg) = rp 3 (dirY (x, y, yneg)) := (rp3_dirY (x, y, yneg)).symm
  simp only [hx3, hy3] at hcov
  rcases coverW_cases hκ hρ hcov with ⟨hl, hr, hk⟩ | ⟨hl, hr, hk⟩ | ⟨hl, hr, hk⟩ | ⟨hl, hr, hk⟩ |
    ⟨hl, hr, hk⟩ | ⟨hl, hr, hk⟩
  · exact gen 1 1 (Or.inl rfl) (Or.inl rfl) hl hr
      ⟨0, fun k _ => prog3_one H.acc3 H.s g ha hb hc x _ rfl hm hk k⟩
  · exact gen 2 1 (Or.inr (Or.inl rfl)) (Or.inl rfl) hl hr
      ⟨0, fun k _ => prog3_one H.acc3 H.s g ha hb hc x _ rfl hm hk k⟩
  · exact gen 4 1 (Or.inr (Or.inr rfl)) (Or.inl rfl) hl hr
      ⟨0, fun k _ => prog3_one H.acc3 H.s g ha hb hc x _ rfl hm hk k⟩
  · exact gen 1 3 (Or.inl rfl) (Or.inr rfl) hl hr (prog3_three H.acc3 H.s g ha hb hc x _ rfl hm hk)
  · exact gen 2 3 (Or.inr (Or.inl rfl)) (Or.inr rfl) hl hr
      (prog3_three H.acc3 H.s g ha hb hc x _ rfl hm hk)
  · exact gen 4 3 (Or.inr (Or.inr rfl)) (Or.inr rfl) hl hr
      (prog3_three H.acc3 H.s g ha hb hc x _ rfl hm hk)

theorem coverAll_testBit {acc2 acc3 : BT ℕ} {s a b c maxm T i : ℕ} {opts : List TermOpt}
    (h : (coverAll acc2 acc3 s a b c maxm T opts).testBit i = true) :
    ∃ o ∈ opts, (optCover acc2 acc3 s a b c maxm T o).testBit i = true := by
  induction opts with
  | nil => simp [coverAll] at h
  | cons o opts ih =>
    have h' : (optCover acc2 acc3 s a b c maxm T o ||| coverAll acc2 acc3 s a b c maxm T opts).testBit i
        = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨o, List.mem_cons_self, h'⟩
    · obtain ⟨o', ho', h''⟩ := ih h'
      exact ⟨o', List.mem_cons_of_mem _ ho', h''⟩

end KimKimOh

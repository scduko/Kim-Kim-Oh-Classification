import KimKimOh.Region

/-!
# Every exception lies in the region (`sec:high`, `sec:finite`, `app:prescriptions`)

`region_cover`: a maximal ternary `S` of minimum at least 2, in a reduced basis, is represented
by `L` or has `P_t ≤ δ ≤ hiOf …` for some `t < 27` with `a ≤ 72`, or `a ≥ 73` within the class
bounds. The class bounds use the profile lists of the class of `a₀` (`classSkip`, `Acap`); the
block bound uses the profiles of the block's chunks (`hiTab`, `hiOf`).
-/

namespace KimKimOh

open GramLattice Tables Primes

theorem thr_eq (s a a₀ g : ℕ) (o : ℕ × ℕ × ℕ) :
    thr s a a₀ g o = a * numO s a₀ g o / denO s a₀ o := by
  unfold thr numO denO
  congr 1
  ring

theorem denO_pos {j s a₀ : ℕ} {P₂ P₃ : List (List (ℕ × ℕ))} {o : ℕ × ℕ × ℕ}
    (ho : o ∈ validOpts j s a₀ P₂ P₃) : 0 < denO s a₀ o := by
  rw [validOpts, List.mem_filter] at ho
  simp only [validOpt, Bool.and_eq_true, decide_eq_true_eq] at ho
  unfold denO
  omega

/-- From `3 P_t D² > 4 N'²` and `3 a² ≤ 4 δ`, `P_t ≤ δ`: the threshold is below `δ`. -/
theorem thr_lt_of_skip {s a a₀ g Pt δ : ℕ} {o : ℕ × ℕ × ℕ} (hden : 0 < denO s a₀ o)
    (hskip : 4 * numO s a₀ g o ^ 2 < 3 * Pt * denO s a₀ o ^ 2) (h3a : 3 * a ^ 2 ≤ 4 * δ)
    (hPt : Pt ≤ δ) : thr s a a₀ g o < δ := by
  rw [thr_eq, Nat.div_lt_iff_lt_mul hden]
  by_contra hc
  push Not at hc
  set N := numO s a₀ g o
  set D := denO s a₀ o
  -- `D δ ≤ a N`, so `D² δ² ≤ a² N² ≤ (4 δ / 3) N²`
  have h1 : (D * δ) ^ 2 ≤ (a * N) ^ 2 := Nat.pow_le_pow_left (by linarith) 2
  have h2 : 3 * (a * N) ^ 2 ≤ 4 * δ * N ^ 2 := by
    have := Nat.mul_le_mul_right (N ^ 2) h3a
    nlinarith
  have h3 : 3 * D ^ 2 * δ ≤ 4 * N ^ 2 := by
    have hδ : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with h | h
      · exfalso
        have hP0 : Pt = 0 := by omega
        rw [hP0] at hskip
        simp at hskip
      · exact h
    have : δ * (3 * D ^ 2 * δ) ≤ δ * (4 * N ^ 2) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hδ
  nlinarith

/-- From `a > ⌊4 N' / 3 D⌋` and `3 a² ≤ 4 δ`: the threshold is below `δ`. -/
theorem thr_lt_of_aBound {s a a₀ g δ : ℕ} {o : ℕ × ℕ × ℕ} (hden : 0 < denO s a₀ o)
    (ha : aBound s a₀ g o < a) (h3a : 3 * a ^ 2 ≤ 4 * δ) : thr s a a₀ g o < δ := by
  unfold aBound at ha
  rw [Nat.div_lt_iff_lt_mul (by positivity)] at ha
  rw [thr_eq, Nat.div_lt_iff_lt_mul hden]
  set N := numO s a₀ g o
  set D := denO s a₀ o
  -- `4 a N < 3 D a² ≤ 4 D δ`
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp at ha
    · exact h
  have : 4 * (a * N) < 4 * (δ * D) := by
    calc 4 * (a * N) = a * (4 * N) := by ring
      _ < a * (a * (3 * D)) := Nat.mul_lt_mul_of_pos_left (by linarith) ha0
      _ = (3 * a ^ 2) * D := by ring
      _ ≤ (4 * δ) * D := Nat.mul_le_mul_right _ h3a
      _ = 4 * (δ * D) := by ring
  omega

theorem pairsOK_mem {j s : ℕ} {L₂ L₃ : List (List (List (ℕ × ℕ)))} {a₀ : ℕ}
    (hok : pairsOK j s L₂ L₃ a₀ = true) {P₂ P₃ : List (List (ℕ × ℕ))}
    (hP : (P₂, P₃) ∈ pairsOf L₂ L₃) : validOpts j s a₀ P₂ P₃ ≠ [] := by
  unfold pairsOK at hok
  rw [List.all_eq_true] at hok
  simpa [List.isEmpty_iff] using hok _ hP

theorem high_lt_of_classSkip {j s : ℕ} {L₂ L₃ : List (List (List (ℕ × ℕ)))} {a a₀ t δ : ℕ}
    (hδ : 0 < δ) (hskip : classSkip j s L₂ L₃ a₀ t = true) (h3a : 3 * a ^ 2 ≤ 4 * δ)
    (hPt : Pc t ≤ δ) : high j s L₂ L₃ a a₀ t < δ := by
  refine high_lt_of_exists hδ fun P₂ P₃ hP => ?_
  unfold classSkip at hskip
  rw [List.all_eq_true] at hskip
  obtain ⟨o, ho, hlt⟩ := List.any_eq_true.mp (hskip _ hP)
  exact ⟨o, ho, thr_lt_of_skip (denO_pos ho) (Nat.blt_eq.mp hlt) h3a hPt⟩

theorem high_lt_of_Acap {j s : ℕ} {L₂ L₃ : List (List (List (ℕ × ℕ)))} {a a₀ t δ : ℕ}
    (hδ : 0 < δ) (hok : pairsOK j s L₂ L₃ a₀ = true) (ha : Acap j s L₂ L₃ a₀ t < a)
    (h3a : 3 * a ^ 2 ≤ 4 * δ) : high j s L₂ L₃ a a₀ t < δ := by
  refine high_lt_of_exists hδ fun P₂ P₃ hP => ?_
  have hne := pairsOK_mem hok hP
  have hle := (le_foldl_max (fun pr : List (List (ℕ × ℕ)) × List (List (ℕ × ℕ)) =>
    minL ((validOpts j s a₀ pr.1 pr.2).map (aBound s a₀ (Windows.gWin t))))
    (pairsOf L₂ L₃) 0).2 _ hP
  obtain ⟨o, ho, hoeq⟩ := List.mem_map.mp (minL_mem (l := (validOpts j s a₀ P₂ P₃).map
    (aBound s a₀ (Windows.gWin t))) (by simpa using hne))
  refine ⟨o, ho, thr_lt_of_aBound (denO_pos ho) ?_ h3a⟩
  unfold Acap at ha
  simp only at hle
  omega

theorem pairsOK_mono {j s a₀ : ℕ} {L₂ L₃ L₂' L₃' : List (List (List (ℕ × ℕ)))}
    (h₂ : ∀ P ∈ L₂', P ∈ L₂) (h₃ : ∀ P ∈ L₃', P ∈ L₃) (hok : pairsOK j s L₂ L₃ a₀ = true) :
    pairsOK j s L₂' L₃' a₀ = true := by
  unfold pairsOK at hok ⊢
  rw [List.all_eq_true] at hok ⊢
  intro pr hpr
  apply hok
  unfold pairsOf at hpr ⊢
  obtain ⟨P₂, hP₂, hpr⟩ := List.mem_flatMap.mp hpr
  obtain ⟨P₃, hP₃, rfl⟩ := List.mem_map.mp hpr
  exact List.mem_flatMap.mpr ⟨P₂, h₂ _ hP₂, List.mem_map.mpr ⟨P₃, h₃ _ hP₃, rfl⟩⟩

/-- For `a₀, a₁ ≥ 73` the valid options agree (all `x > 0`, `s x² ≤ 72`). -/
theorem validOpts_big {j s a₀ a₁ : ℕ} (hs : s ≤ 2) (h₀ : 73 ≤ a₀) (h₁ : 73 ≤ a₁)
    (P₂ P₃ : List (List (ℕ × ℕ))) : validOpts j s a₀ P₂ P₃ = validOpts j s a₁ P₂ P₃ := by
  have hopt : optsOf a₀ P₂ P₃ = optsOf a₁ P₂ P₃ := by
    unfold optsOf
    congr 1
    funext x
    have e0 : decide (a₀ < 73) = false := by simp; omega
    have e1 : decide (a₁ < 73) = false := by simp; omega
    simp only [e0, e1]
  unfold validOpts
  rw [hopt]
  refine List.filter_congr fun o ho => ?_
  obtain ⟨x, hx, hx0, o₂, -, o₃, -, rfl⟩ := mem_optsOf ho
  have hx0' : x ≠ 0 := by rcases hx0 with h | h <;> omega
  have hx6 : x ≤ 6 := by simp [xList] at hx; omega
  have hsx : s * x * x ≤ 72 := by
    have : x * x ≤ 36 := Nat.mul_le_mul hx6 hx6
    calc s * x * x = s * (x * x) := by ring
      _ ≤ 2 * 36 := Nat.mul_le_mul hs this
  unfold validOpt
  simp only
  have e0 : decide (s * x * x < a₀) = true := by simp; omega
  have e1 : decide (s * x * x < a₁) = true := by simp; omega
  have ex : (x != 0) = true := by simpa using hx0'
  simp [e0, e1, ex]

theorem a0Of_spec {a : ℕ} (h : 73 ≤ a) :
    73 ≤ a0Of a ∧ a0Of a ≤ 84 ∧ a0Of a ≤ a ∧ a0Of a % 4 = a % 4 ∧ a0Of a % 3 = a % 3 := by
  unfold a0Of; omega

/-- The data of the block bounds for a host: the mask classes, the chunk indices, and the checked
facts relating them to the profile masks and the class-level options. `hpairs` is Certificate 4.1
(`cert:progressions`) for `2 ≤ a₀ ≤ 84`; for `a ≥ 73` the options depend only on `a mod 12`
(`validOpts_big`, `a0Of_spec`). -/
structure RegionData (H : HostSpec) where
  ml2 : ℕ → List ℕ
  ml3 : ℕ → List ℕ
  pi2 : ℕ
  pi3 : ℕ
  hm2 : ∀ blk < 256, mget H.pm2 blk = (ml2 (blk / 32 % 4)).getD (pget pi2 blk) 0
  hm3 : ∀ blk < 729, mget H.pm3 blk = (ml3 (blk / 81 % 3)).getD (pget pi3 blk) 0
  hpairs : ∀ a₀, 2 ≤ a₀ → a₀ ≤ 84 →
    pairsOK H.j H.s (H.prof2 (a₀ % 4)) (H.prof3 (a₀ % 3)) a₀ = true

/-- **The region of blocks left by `sec:high`**: the intervals of Certificate 4.2 (`cert:ranges`),
refined by the block bound `H_j(B, t)` of `sec:finite`. -/
def InRegion (H : HostSpec) (R : RegionData H) (a b c δ : ℕ) : Prop :=
  ∃ t < 27, Pc t ≤ δ ∧ δ < Pc (t + 1) ∧
    (a ≤ 72 ∨ (classSkip H.j H.s (H.prof2 (a0Of a % 4)) (H.prof3 (a0Of a % 3)) (a0Of a) t = false ∧
      a ≤ Acap H.j H.s (H.prof2 (a0Of a % 4)) (H.prof3 (a0Of a % 3)) (a0Of a) t)) ∧
    δ ≤ hiOf (hiTab H.j H.s H.prof2 H.prof3 R.ml2 R.ml3 a t) R.pi2 R.pi3 a b c

set_option maxHeartbeats 2000000 in
/-- **Every exception lies in the region.** -/
theorem region_cover (H : HostSpec) (R : RegionData H)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) (hred : (ternOf S).IsReduced)
    (ha2 : 2 ≤ (ternOf S).a) :
    L.Represents S ∨ InRegion H R (ternOf S).a.toNat (ternOf S).b.toNat (ternOf S).c.toNat
      (ternOf S).delta.toNat := by
  set g := ternOf S with hg
  have hδ0 : 0 < g.delta := delta_pos S
  have hb0 := hred.b_nonneg
  have hac := hred.a_le_c
  set a := g.a.toNat with hadef
  set b := g.b.toNat with hbdef
  set c := g.c.toNat with hcdef
  set δ := g.delta.toNat with hδdef
  have haZ : (a : ℤ) = g.a := by omega
  have hbZ : (b : ℤ) = g.b := by omega
  have hcZ : (c : ℤ) = g.c := by omega
  have hδZ : (δ : ℤ) = g.delta := by omega
  have ha2' : 2 ≤ a := by omega
  have hδpos : 0 < δ := by omega
  have h3a : 3 * a ^ 2 ≤ 4 * δ := by
    have := three_a_sq_le hred
    have : ((3 * a ^ 2 : ℕ) : ℤ) ≤ ((4 * δ : ℕ) : ℤ) := by push_cast; rw [haZ, hδZ]; exact this
    exact_mod_cast this
  have hs2 : H.s ≤ 2 := by rcases H.hs with h | h <;> omega
  -- the class `a₀`
  obtain ⟨a₀, hle, h4, h3, h2', h84, hsm, hbg⟩ : ∃ a₀, a₀ ≤ a ∧ a₀ % 4 = a % 4 ∧ a₀ % 3 = a % 3 ∧
      2 ≤ a₀ ∧ a₀ ≤ 84 ∧ (a < 73 → a₀ = a) ∧ (73 ≤ a → a₀ = a0Of a) := by
    by_cases h : a < 73
    · exact ⟨a, le_rfl, rfl, rfl, ha2', by omega, fun _ => rfl, fun h' => by omega⟩
    · have := a0Of_spec (show 73 ≤ a by omega)
      exact ⟨a0Of a, by omega, by omega, by omega, by omega, by omega, fun h' => by omega,
        fun _ => rfl⟩
  have hr8a : r8 g.a % 4 = a % 4 := by unfold r8; omega
  have hrp3a : rp 3 g.a = a % 3 := by unfold rp; omega
  have hch2 := chunk2_eq (by omega : g.a = a) (by omega : g.b = b) (by omega : g.c = c)
  have hch3 := chunk3_eq (by omega : g.a = a) (by omega : g.b = b) (by omega : g.c = c)
  have hb2 : blk2 (a % 8) (b % 4) (c % 8) < 256 := by unfold blk2; omega
  have hb3 : blk3 (a % 9) (b % 9) (c % 9) < 729 := by unfold blk3; omega
  have hc2 : blk2 (a % 8) (b % 4) (c % 8) / 32 % 4 = a % 4 := by unfold blk2; omega
  have hc3 : blk3 (a % 9) (b % 9) (c % 9) / 81 % 3 = a % 3 := by unfold blk3; omega
  have hr8 : r8 g.a % 4 = a₀ % 4 := by unfold r8; omega
  have hrp3 : rp 3 g.a = a₀ % 3 := by unfold rp; omega
  have hLc2 : ∀ P ∈ maskedProfs (H.prof2 (r8 g.a % 4)) (mget H.pm2 (chunk2 g)),
      P ∈ H.prof2 (a₀ % 4) := fun P hP => hr8 ▸ mem_maskedProfs hP
  have hLc3 : ∀ P ∈ maskedProfs (H.prof3 (rp 3 g.a)) (mget H.pm3 (chunk3 g)),
      P ∈ H.prof3 (a₀ % 3) := fun P hP => hrp3 ▸ mem_maskedProfs hP
  have hokc := R.hpairs a₀ h2' h84
  have hsmall : g.a < 73 → a₀ = g.a.toNat := fun h => hsm (by omega)
  have hbig : 73 ≤ g.a → 73 ≤ a₀ := fun h => by have := a0Of_spec (show 73 ≤ a by omega); omega
  -- the interval of `δ`
  obtain ⟨t, htP, htP'⟩ := exists_P_interval hδpos
  have htPZ : (P t : ℤ) ≤ g.delta := by rw [← hδZ]; exact_mod_cast htP
  have htP'Z : g.delta < (P (t + 1) : ℤ) := by rw [← hδZ]; exact_mod_cast htP'
  by_cases ht27 : 27 ≤ t
  · left
    exact represents_of_tail H hK L hL S hmax hred t ht27 htPZ htP'Z a₀ hle hsmall hbig _ _ hLc2 hLc3 hokc
  push Not at ht27
  rw [P_eq (by omega)] at htP
  rw [P_eq (by omega)] at htP'
  by_cases hcls : 73 ≤ a ∧ (classSkip H.j H.s (H.prof2 (a0Of a % 4)) (H.prof3 (a0Of a % 3))
      (a0Of a) t = true ∨ Acap H.j H.s (H.prof2 (a0Of a % 4)) (H.prof3 (a0Of a % 3)) (a0Of a) t < a)
  · left
    obtain ⟨h73, hcls⟩ := hcls
    have ha0e := hbg h73
    refine represents_of_high_lt H hK L hL S hmax hred t htP'Z a₀ hle hsmall hbig _ _ hLc2 hLc3 hokc ?_
    rw [ha0e]
    rcases hcls with hc | hc
    · exact high_lt_of_classSkip hδpos hc h3a htP
    · rw [ha0e] at hokc
      exact high_lt_of_Acap hδpos hokc hc h3a
  -- the block bound
  by_cases hreg : δ ≤ hiOf (hiTab H.j H.s H.prof2 H.prof3 R.ml2 R.ml3 a t) R.pi2 R.pi3 a b c
  · right
    refine ⟨t, ht27, htP, htP', ?_, hreg⟩
    by_cases h72 : a ≤ 72
    · exact Or.inl h72
    · right
      push Not at hcls
      have := hcls (by omega)
      exact ⟨by simpa using this.1, by omega⟩
  · left
    push Not at hreg
    rw [hiOf_hiTab _ _ _ _ _ _ ht27] at hreg
    unfold hiEntry at hreg
    have hhigh := (min_lt_iff.mp hreg).resolve_right (by omega)
    -- the chunk lists are the masked profiles of the actual chunks
    have hm2 := R.hm2 _ hb2
    have hm3 := R.hm3 _ hb3
    rw [hc2] at hm2
    rw [hc3] at hm3
    refine represents_of_high_lt H hK L hL S hmax hred t htP'Z g.a.toNat le_rfl (fun _ => rfl) (fun h => hbig h |>.trans hle)
      (maskedProfs (H.prof2 (a % 4))
        ((R.ml2 (a % 4)).getD (pget R.pi2 (blk2 (a % 8) (b % 4) (c % 8))) 0))
      (maskedProfs (H.prof3 (a % 3))
        ((R.ml3 (a % 3)).getD (pget R.pi3 (blk3 (a % 9) (b % 9) (c % 9))) 0))
      (fun P hP => ?_) (fun P hP => ?_) ?_ hhigh
    · rw [hr8a, hch2, hm2] at hP; exact hP
    · rw [hrp3a, hch3, hm3] at hP; exact hP
    · -- the class options at `a`
      refine pairsOK_mono (fun P hP => mem_maskedProfs hP) (fun P hP => mem_maskedProfs hP) ?_
      by_cases h84 : a ≤ 84
      · exact R.hpairs a ha2' h84
      · have h73 : 73 ≤ a := by omega
        obtain ⟨h1, h2, -, h4', h3'⟩ := a0Of_spec h73
        have hok := R.hpairs (a0Of a) (by omega) h2
        rw [h4', h3'] at hok
        unfold pairsOK at hok ⊢
        rw [List.all_eq_true] at hok ⊢
        intro pr hpr
        rw [validOpts_big hs2 (show 73 ≤ a by omega) h1]
        exact hok pr hpr

end KimKimOh

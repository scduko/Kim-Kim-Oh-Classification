import KimKimOh.HighBound

/-!
# The first pass of `sec:finite`: one direction for a whole binary block

For a binary block `B = (a, b, c)` and a direction `α = (x, y)`, the local tables give a step
`m = w₂ w₃` for `k` that works for every maximal completion of the block's residue
(`chunk2_spec`, `chunk3_spec`). At a prime `p ≥ 5` dividing `Δ`, at most `ν_p` classes of `k`
fail the local test (`atMostClasses_weight_not_okAt`): `ν_p = 1` if `p ∤ δ` or `B ≡ 0 (mod p)`,
and `ν_p = 2` otherwise (`lem:scalar-slice`). If `Σ ν_p ⌈G / p⌉ < G` and `s a (m G)² < 3 Δ`, then
among `G` consecutive terms of the progression near the centre one passes every test and gives a
positive correction (`block_rep`).
-/

namespace KimKimOh

open GramLattice Tables Excluded

/-! ### Periodicity of the local test at `p ≥ 5` -/

theorem okAt_congr {p : ℕ} {C C' : Tern} (j : ℤ) (ha : (p : ℤ) ∣ C.a - C'.a) (hb : (p : ℤ) ∣ C.b - C'.b)
    (hc : (p : ℤ) ∣ C.c - C'.c) (hd : (p : ℤ) ∣ C.d - C'.d) (he : (p : ℤ) ∣ C.e - C'.e)
    (hf : (p : ℤ) ∣ C.f - C'.f) : C.OkAt j p ↔ C'.OkAt j p := by
  have cast_eq : ∀ {u v : ℤ}, (p : ℤ) ∣ u - v → (u : ZMod p) = (v : ZMod p) := fun h =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr (by rw [← neg_sub, dvd_neg]; exact h)
  have dvd_iff : ∀ {u v : ℤ}, (u : ZMod p) = (v : ZMod p) → ((p : ℤ) ∣ u ↔ (p : ℤ) ∣ v) := by
    intro u v h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, h]
  have ea := cast_eq ha; have eb := cast_eq hb; have ec := cast_eq hc
  have ed := cast_eq hd; have ee := cast_eq he; have ef := cast_eq hf
  have hrank : C.RankLeOneMod p ↔ C'.RankLeOneMod p := by
    unfold Tern.RankLeOneMod Tern.minors
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have key : ∀ (u v : ℤ), (u : ZMod p) = (v : ZMod p) → ((p : ℤ) ∣ u ↔ (p : ℤ) ∣ v) :=
      fun u v h => dvd_iff h
    rw [key (C.a * C.c - C.b * C.b) (C'.a * C'.c - C'.b * C'.b) (by push_cast; rw [ea, eb, ec]),
      key (C.a * C.f - C.d * C.d) (C'.a * C'.f - C'.d * C'.d) (by push_cast; rw [ea, ed, ef]),
      key (C.c * C.f - C.e * C.e) (C'.c * C'.f - C'.e * C'.e) (by push_cast; rw [ec, ee, ef]),
      key (C.a * C.e - C.b * C.d) (C'.a * C'.e - C'.b * C'.d) (by push_cast; rw [ea, ee, eb, ed]),
      key (C.b * C.e - C.c * C.d) (C'.b * C'.e - C'.c * C'.d) (by push_cast; rw [eb, ee, ec, ed]),
      key (C.b * C.f - C.d * C.e) (C'.b * C'.f - C'.d * C'.e) (by push_cast; rw [eb, ef, ed, ee])]
  have hsq : C.HasDiagSquareClass j p ↔ C'.HasDiagSquareClass j p := by
    unfold Tern.HasDiagSquareClass
    have key : ∀ (u v w : ℤ), (u : ZMod p) = (v : ZMod p) →
        ((p : ℤ) ∣ u - w ↔ (p : ℤ) ∣ v - w) := fun u v w h => dvd_iff (by push_cast; rw [h])
    constructor <;> rintro ⟨u, hu, h⟩ <;> refine ⟨u, hu, ?_⟩
    · rwa [← key C.a C'.a _ ea, ← key C.c C'.c _ ec, ← key C.f C'.f _ ef]
    · rwa [key C.a C'.a _ ea, key C.c C'.c _ ec, key C.f C'.f _ ef]
  unfold Tern.OkAt Tern.RankGeTwoMod
  rw [hrank, hsq]

/-- The local test at `p` of the corrections depends only on `k mod p`. -/
theorem okAt_periodic (g : Tern) (s x y j : ℤ) (p : ℕ) :
    Periodic p (fun k => ¬ (g.corr s x y k).OkAt j p) := by
  intro k k' hk
  have e : ∀ u : ℤ, (p : ℤ) ∣ u * (k - k') := fun u => dvd_mul_of_dvd_right hk u
  show ¬ _ ↔ ¬ _
  refine not_congr (okAt_congr (C := g.corr s x y k) (C' := g.corr s x y k') j ?_ ?_ ?_ ?_ ?_ ?_)
  · simp [Tern.corr]
  · simp [Tern.corr]
  · simp [Tern.corr]
  · simp only [Tern.corr]; convert e (-(s * x)) using 1; ring
  · simp only [Tern.corr]; convert e (-(s * y)) using 1; ring
  · simp only [Tern.corr]; convert e (-(s * (k + k'))) using 1; ring

/-! ### The classes of `k` failing at `p ≥ 5` -/

/-- The weight `ν_p`: 2 if `p ∣ δ` and `B ≢ 0 (mod p)`, and 1 otherwise. -/
def Tern.weight (g : Tern) (p : ℕ) : ℕ :=
  if (p : ℤ) ∣ g.delta ∧ ¬ ((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c) then 2 else 1

/-! ### The block lemma -/

/-- **The classes of `k` failing at `p ≥ 5`**: at most `ν_p` (`lem:scalar-slice`), when `B` and
`α` do not both vanish modulo `p`. -/
theorem atMostClasses_weight_not_okAt {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {s : ℤ} (hs : s = 1 ∨ s = 2) (j : ℤ)
    (g : Tern) (x y : ℤ) (hG : g.NonzeroMod p)
    (hBα : ¬ ((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c ∧ (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y)) :
    AtMostClasses p (g.weight p) (fun k => ¬ (g.corr s x y k).OkAt j p) := by
  unfold Tern.weight
  split_ifs with h
  · exact atMostClasses_not_okAt_of_rank (scalar_slice hp5 hs g x y hG hBα)
  · refine atMostClasses_not_okAt_of_rank (scalar_slice_one hp5 hs g x y hG hBα ?_)
    by_cases hδ : (p : ℤ) ∣ g.delta
    · exact Or.inr (Or.inl (not_not.mp fun h' => h ⟨hδ, h'⟩))
    · exact Or.inl hδ

/-- **The general block lemma.** Let `S` be maximal, `α = (x, y)`, and suppose the corrections
are locally represented at 2 on a class of `k` modulo `w₂ ∈ {1, 2, 4}` and at 3 on a class modulo
`w₃ ∈ {1, 3}`. Let `Om` be a set of primes at which every correction passes the test, and suppose
`B` and `α` do not both vanish at the other primes `p ≥ 5` dividing `Δ`. If
`Σ_{p ∣ Δ, p ∉ Om} ν_p ⌈G / p⌉ < G` and `s (w₂ w₃ G)² δ² < 4 D Δ`, then `L` represents `S`. -/
theorem block_rep_core (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) (x y : ℤ)
    (w₂ w₃ : ℕ) (hw₂ : w₂ = 1 ∨ w₂ = 2 ∨ w₂ = 4) (hw₃ : w₃ = 1 ∨ w₃ = 3)
    (h2 : ∃ k₂ : ℤ, ∀ k : ℤ, (w₂ : ℤ) ∣ k - k₂ →
      LocallyRepresents H.K.gram ((ternOf S).corr H.s x y k).toMatrix 2)
    (h3 : ∃ k₃ : ℤ, ∀ k : ℤ, (w₃ : ℤ) ∣ k - k₃ →
      LocallyRepresents H.K.gram ((ternOf S).corr H.s x y k).toMatrix 3)
    (Om : Finset ℕ) (hOm : ∀ p ∈ Om, ∀ k : ℤ, ((ternOf S).corr H.s x y k).OkAt H.j p)
    (hBα : ∀ p ∈ bigPrimesOf ((ternOf S).corrDelta H.s x y), p ∉ Om →
      ¬ ((p : ℤ) ∣ (ternOf S).a ∧ (p : ℤ) ∣ (ternOf S).b ∧ (p : ℤ) ∣ (ternOf S).c ∧
        (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y))
    (G : ℕ) (hG0 : 0 < G)
    (hsum : ∑ p ∈ bigPrimesOf ((ternOf S).corrDelta H.s x y) \ Om,
      (ternOf S).weight p * ((G + p - 1) / p) < G)
    (hcert : (H.s : ℤ) * ((w₂ * w₃ * G : ℕ) : ℤ) ^ 2 * (ternOf S).delta ^ 2 <
      4 * (ternOf S).det * (ternOf S).corrDelta H.s x y) :
    L.Represents S := by
  classical
  set g := ternOf S with hg
  have ha : 0 < g.a := a_pos S
  have hδ : 0 < g.delta := delta_pos S
  have hD : 0 < g.det := det_pos S
  have hsymm : ∀ i j, S.gram i j = S.gram j i := fun i j => S.gram_comm i j
  have hGp : ∀ p : ℕ, p.Prime → g.NonzeroMod p := fun p hp =>
    nonzeroMod_of_isMaximal hmax hsymm hp
  have hs0 : (0 : ℤ) < H.s := H.s_pos
  have hsZ : (H.s : ℤ) = 1 ∨ (H.s : ℤ) = 2 := by rcases H.hs with h | h <;> simp [h]
  set Δ := g.corrDelta H.s x y with hΔdef
  obtain ⟨k₂, hk₂⟩ := h2
  obtain ⟨k₃, hk₃⟩ := h3
  set m : ℕ := w₂ * w₃ with hm
  have hm0 : 0 < m := by
    rcases hw₂ with h | h | h <;> rcases hw₃ with h' | h' <;> simp [hm, h, h']
  have hmdvd : m ∣ 12 := by
    rcases hw₂ with h | h | h <;> rcases hw₃ with h' | h' <;> simp [hm, h, h']
  have hloc : ∀ k : ℤ, (m : ℤ) ∣ k - (9 * k₂ - 8 * k₃) →
      LocallyRepresents H.K.gram (g.corr H.s x y k).toMatrix 2 ∧
        LocallyRepresents H.K.gram (g.corr H.s x y k).toMatrix 3 := by
    intro k hk
    have e2 : (w₂ : ℤ) ∣ k - k₂ := by
      have hd : (w₂ : ℤ) ∣ (m : ℤ) := by push_cast [hm]; exact dvd_mul_right _ _
      have h4 : (w₂ : ℤ) ∣ 8 := by rcases hw₂ with h | h | h <;> rw [h] <;> norm_num
      have : k - k₂ = (k - (9 * k₂ - 8 * k₃)) + 8 * (k₂ - k₃) := by ring
      rw [this]; exact dvd_add (hd.trans hk) (dvd_mul_of_dvd_left h4 _)
    have e3 : (w₃ : ℤ) ∣ k - k₃ := by
      have hd : (w₃ : ℤ) ∣ (m : ℤ) := by push_cast [hm]; exact dvd_mul_left _ _
      have h9 : (w₃ : ℤ) ∣ 9 := by rcases hw₃ with h | h <;> rw [h] <;> norm_num
      have : k - k₃ = (k - (9 * k₂ - 8 * k₃)) + 9 * (k₂ - k₃) := by ring
      rw [this]; exact dvd_add (hd.trans hk) (dvd_mul_of_dvd_left h9 _)
    exact ⟨hk₂ k e2, hk₃ k e3⟩
  have hcert' : (H.s : ℤ) * ((m : ℤ) * G) ^ 2 * g.delta ^ 2 < 4 * g.det * Δ := by
    have := hcert; push_cast [hm] at this ⊢; linarith
  have hΔpos : 0 < Δ := by
    have : (0 : ℤ) ≤ (H.s : ℤ) * ((m : ℤ) * G) ^ 2 * g.delta ^ 2 := by positivity
    by_contra h0; push Not at h0
    nlinarith
  obtain ⟨k₀, hk₀, hposk⟩ := exists_window g ha hδ hD hs0 (M := (m : ℤ)) (by exact_mod_cast hm0)
    (9 * k₂ - 8 * k₃) G hcert'
  set P := bigPrimesOf Δ \ Om with hPdef
  have hP : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ m ∧ Periodic p (fun k => ¬ (g.corr H.s x y k).OkAt H.j p) ∧
      AtMostClasses p (g.weight p) (fun k => ¬ (g.corr H.s x y k).OkAt H.j p) := by
    intro p hp
    rw [hPdef, Finset.mem_sdiff] at hp
    obtain ⟨hpp, h5, -⟩ := (mem_bigPrimesOf hΔpos.ne').mp hp.1
    have : Fact p.Prime := ⟨hpp⟩
    refine ⟨hpp, fun hdvd => ?_, okAt_periodic g H.s x y H.j p, ?_⟩
    · have h12 : p ∣ 12 := hdvd.trans hmdvd
      rcases (Nat.Prime.dvd_mul hpp).mp (show p ∣ 4 * 3 from h12) with h' | h'
      · have := Nat.le_of_dvd (by norm_num) h'; omega
      · have := Nat.le_of_dvd (by norm_num) h'; omega
    · exact atMostClasses_weight_not_okAt h5 hsZ H.j g x y (hGp p hpp) (hBα p hp.1 hp.2)
  obtain ⟨i, hi, hgood⟩ := Windows.ap_sieve k₀ m G P g.weight
    (fun p k => ¬ (g.corr H.s x y k).OkAt H.j p) hP hsum
  obtain ⟨hCa, hCδ, hCD⟩ := hposk i hi
  have hloc23 := hloc (k₀ + m * i) (by
    obtain ⟨c, hc⟩ := hk₀; exact ⟨c + i, by linear_combination hc⟩)
  refine hL.trans (represents_of_corr H.K hK hs0 S x y (k₀ + m * i) hCa hCδ hCD fun p hp => ?_)
  rcases prime_cases hp with rfl | rfl | h5
  · exact hloc23.1
  · exact hloc23.2
  · refine H.okAt_sound p hp h5 _ ?_
    by_cases hom : p ∈ Om
    · exact hOm p hom _
    by_cases hpk : p ∈ bigPrimesOf Δ
    · exact not_not.mp (hgood p (Finset.mem_sdiff.mpr ⟨hpk, hom⟩))
    · left
      refine Tern.rankGeTwoMod_corr g H.s x y _ fun hdvd => hpk ?_
      exact (mem_bigPrimesOf hΔpos.ne').mpr ⟨hp, h5, hdvd⟩

/-- **One direction for a block, with a positivity certificate.** As `block_rep`, with the
hypothesis `s (w₂ w₃ G)² δ² < 4 D Δ` in place of `s a (w₂ w₃ G)² < 3 Δ`. -/
theorem block_rep_cert (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram)
    (x y : ℤ) (hxy : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y))
    (hw₂ : wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) = 1 ∨
      wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) = 2 ∨
      wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) = 4)
    (hw₃ : wget H.wt3 (chunk3 (ternOf S)) (3 * rp 3 x + rp 3 y) = 1 ∨
      wget H.wt3 (chunk3 (ternOf S)) (3 * rp 3 x + rp 3 y) = 3)
    (G : ℕ) (hG0 : 0 < G)
    (hsum : ∑ p ∈ bigPrimesOf ((ternOf S).corrDelta H.s x y),
      (ternOf S).weight p * ((G + p - 1) / p) < G)
    (hcert' : (H.s : ℤ) *
      ((wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) *
        wget H.wt3 (chunk3 (ternOf S)) (3 * rp 3 x + rp 3 y) * G : ℕ) : ℤ) ^ 2 * (ternOf S).delta ^ 2 <
      4 * (ternOf S).det * (ternOf S).corrDelta H.s x y) :
    L.Represents S := by
  classical
  set g := ternOf S with hg
  have hmax' : IsMaximal g.toMatrix := by rw [hg, ternOf_toMatrix]; exact hmax
  obtain ⟨k₂, hk₂⟩ := (chunk2_spec H.acc2 H.s H.prof2 H.pm2 H.wt2 H.ok2 g hmax').2 x y hw₂
  obtain ⟨k₃, hk₃⟩ := (chunk3_spec H.acc3 H.s H.prof3 H.pm3 H.wt3 H.ok3 g hmax').2 x y hw₃
  refine block_rep_core H hK L hL S hmax x y _ _ hw₂ hw₃
    ⟨k₂, fun k hk => H.acc2_sound _ (hk₂ k hk)⟩ ⟨k₃, fun k hk => H.acc3_sound _ (hk₃ k hk)⟩ ∅
    (fun p hp => by simp at hp) (fun p hp _ h => ?_) G hG0 (by simpa using hsum) hcert'
  obtain ⟨hpf, h5⟩ := Finset.mem_filter.mp hp
  exact hxy p (Nat.prime_of_mem_primeFactors hpf) h5 ⟨h.2.2.2.1, h.2.2.2.2⟩

/-- **One direction for a block.** Let `S` be maximal in a reduced basis and `α = (x, y)` a
direction with no prime `p ≥ 5` dividing both entries. Let `w₂, w₃` be the table steps of `k` for
the chunks of `S` and `α` (1, 2 or 4 at 2; 1 or 3 at 3). If `Σ_{p ≥ 5, p ∣ Δ} ν_p ⌈G / p⌉ < G`
and `s a (w₂ w₃ G)² < 3 Δ`, then `L` represents `S`. -/
theorem block_rep (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) (hred : (ternOf S).IsReduced)
    (x y : ℤ) (hxy : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y))
    (hw₂ : wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) = 1 ∨
      wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) = 2 ∨
      wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) = 4)
    (hw₃ : wget H.wt3 (chunk3 (ternOf S)) (3 * rp 3 x + rp 3 y) = 1 ∨
      wget H.wt3 (chunk3 (ternOf S)) (3 * rp 3 x + rp 3 y) = 3)
    (G : ℕ) (hG0 : 0 < G)
    (hsum : ∑ p ∈ bigPrimesOf ((ternOf S).corrDelta H.s x y),
      (ternOf S).weight p * ((G + p - 1) / p) < G)
    (hpos : (H.s : ℤ) * (ternOf S).a *
      ((wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) *
        wget H.wt3 (chunk3 (ternOf S)) (3 * rp 3 x + rp 3 y) * G : ℕ) : ℤ) ^ 2 <
      3 * (ternOf S).corrDelta H.s x y) :
    L.Represents S := by
  have ha : 0 < (ternOf S).a := a_pos S
  have hδ : 0 < (ternOf S).delta := delta_pos S
  have hh := hred.height
  refine block_rep_cert H hK L hL S hmax x y hxy hw₂ hw₃ G hG0 hsum ?_
  set M : ℤ := ((wget H.wt2 (chunk2 (ternOf S)) (4 * r4 x + r4 y) *
    wget H.wt3 (chunk3 (ternOf S)) (3 * rp 3 x + rp 3 y) * G : ℕ) : ℤ)
  have hΔpos : 0 < (ternOf S).corrDelta H.s x y := by
    have : (0 : ℤ) ≤ (H.s : ℤ) * (ternOf S).a * M ^ 2 := by positivity
    linarith
  have h2 : (H.s : ℤ) * (ternOf S).a * M ^ 2 * (ternOf S).delta ^ 2 <
      3 * (ternOf S).corrDelta H.s x y * (ternOf S).delta ^ 2 :=
    mul_lt_mul_of_pos_right hpos (by positivity)
  have h3 : 3 * (ternOf S).corrDelta H.s x y * (ternOf S).delta ^ 2 ≤
      4 * (ternOf S).a * (ternOf S).det * (ternOf S).corrDelta H.s x y := by nlinarith
  have h4 : (ternOf S).a * ((H.s : ℤ) * M ^ 2 * (ternOf S).delta ^ 2) <
      (ternOf S).a * (4 * (ternOf S).det * (ternOf S).corrDelta H.s x y) := by nlinarith
  exact lt_of_mul_lt_mul_left h4 ha.le

end KimKimOh

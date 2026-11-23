import KimKimOh.TermCover
import KimKimOh.Overlattice

/-!
# The terminal enumeration and its witnesses (`sec:finite`, `app:bounded`)

* `locOK_sound`: a local check at `p = 2, 3` gives `C` over `ℤ_p`, directly or through an
  index-`p` overlattice (`enlarge_eq`), since `Xᵀ K X ≡ C'` gives `(XM)ᵀ K (XM) ≡ Mᵀ C' M`.
* `okAt_of_sq`: at a prime `p ≥ 5` dividing every 2×2 minor of `C`, a square-class certificate
  gives a diagonal entry in the square class of `j`.
* `rep_of_witOK`: a witness gives `L ⊇ S` (`represents_of_corr`).
* `mem_liftsOf`: a reduced maximal ternary with normalized signs, leading block `(a, b, c)`, a
  pending class and `D ≤ U` is enumerated.
* `termOK_sound`: **the terminal check of a block** gives `L ⊇ S` for every reduced maximal `S`
  with normalized signs and leading block `(a, b, c)`.
-/

namespace KimKimOh

open GramLattice Tables Matrix

/-! ### Local representations through overlattices -/

theorem locRep_conj {κ : Type*} [Fintype κ] {K : Matrix κ κ ℤ} {G : Matrix (Fin 3) (Fin 3) ℤ}
    (M : Matrix (Fin 3) (Fin 3) ℤ) {p : ℕ} (h : LocallyRepresents K G p) :
    LocallyRepresents K (Mᵀ * G * M) p := by
  intro k
  obtain ⟨X, hX⟩ := h k
  refine ⟨X * M, fun i j => ?_⟩
  have e : (X * M)ᵀ * K * (X * M) - Mᵀ * G * M = Mᵀ * (Xᵀ * K * X - G) * M := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Finset.dvd_sum fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.dvd_sum fun m _ => ?_
  rw [Matrix.sub_apply]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hX m l) _) _

theorem enlT_toMatrix (C : Tern) (p : ℤ) (k : ℕ) (hk : k < 3) (x₀ x₁ x₂ : ℤ) :
    (enlT C p k x₀ x₁ x₂).toMatrix = enlargeGram C.toMatrix p ⟨k, hk⟩ ![x₀, x₁, x₂] := by
  interval_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [enlT, enlargeGram, Tern.toMatrix, mulVec, dotProduct, Fin.sum_univ_three, sq]

/-- **The local check at `p`**, directly or through an overlattice. -/
theorem locOK_sound {κ : Type*} [Fintype κ] {K : Matrix κ κ ℤ} {acc : Tern → Bool} {p : ℕ}
    (hp : 0 < p) (hacc : ∀ g : Tern, acc g = true → LocallyRepresents K g.toMatrix p) {C : Tern}
    {e : ℕ} (h : locOK acc p C e = true) : LocallyRepresents K C.toMatrix p := by
  unfold locOK at h
  cases he : Nat.beq e 0 with
  | true => rw [he, Bool.cond_true] at h; exact hacc C h
  | false =>
    rw [he, Bool.cond_false] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hpiv, hdiv⟩, hacc'⟩ := h
    set z := (e - 1) / 3
    have hk : (e - 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    set x : Fin 3 → ℤ := ![(digit3 z 0 : ℤ), (digit3 z 1 : ℤ), (digit3 z 2 : ℤ)] with hx
    have hpiv' := Nat.eq_of_beq_eq_true hpiv
    have hxk : x ⟨(e - 1) % 3, hk⟩ = 1 := by
      have h3 : (e - 1) % 3 = 0 ∨ (e - 1) % 3 = 1 ∨ (e - 1) % 3 = 2 := by omega
      rcases h3 with h3 | h3 | h3 <;> simp only [hx, h3] at hpiv' ⊢ <;> simp [hpiv']
    unfold enlDiv at hdiv
    simp only [Bool.and_eq_true, beq_iff_eq] at hdiv
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, hQ⟩ := hdiv
    have hGx : ∀ i, (p : ℤ) ∣ (C.toMatrix *ᵥ x) i := by
      intro i
      fin_cases i
      · exact Int.dvd_of_emod_eq_zero (by simpa [hx, Tern.toMatrix, mulVec, dotProduct,
          Fin.sum_univ_three] using h0)
      · exact Int.dvd_of_emod_eq_zero (by simpa [hx, Tern.toMatrix, mulVec, dotProduct,
          Fin.sum_univ_three] using h1)
      · exact Int.dvd_of_emod_eq_zero (by simpa [hx, Tern.toMatrix, mulVec, dotProduct,
          Fin.sum_univ_three] using h2)
    have hQ' : (p : ℤ) ^ 2 ∣ x ⬝ᵥ C.toMatrix *ᵥ x := by
      refine Int.dvd_of_emod_eq_zero ?_
      rw [sq]
      convert hQ using 2
      simp [hx, Tern.toMatrix, mulVec, dotProduct, Fin.sum_univ_three]
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    have hsym : ∀ i j, C.toMatrix i j = C.toMatrix j i := by
      intro i j; fin_cases i <;> fin_cases j <;> rfl
    have heq := enlarge_eq C.toMatrix hsym hp0 ⟨(e - 1) % 3, hk⟩ x hxk hGx hQ'
    have hloc := hacc _ hacc'
    rw [enlT_toMatrix C p _ hk] at hloc
    rw [← heq]
    exact locRep_conj _ hloc

/-! ### The primes from 5 -/

theorem dvd_minorsGcd_aux {p : ℕ} : ∀ (l : List ℤ), (∀ m ∈ l, (p : ℤ) ∣ m) →
    p ∣ (List.rec 0 (fun m _ r => Nat.gcd m.natAbs r) l : ℕ)
  | [], _ => dvd_zero p
  | n :: l, h => Nat.dvd_gcd (Int.natCast_dvd.mp (h n List.mem_cons_self))
      (dvd_minorsGcd_aux l fun m hm => h m (List.mem_cons_of_mem _ hm))

/-- **The test at a prime `p ≥ 5`** from the square-class certificates. -/
theorem okAt_of_sq {j : ℕ} {C : Tern} {sq : List SquareCert}
    (hstrip : stripL SquareCert.q sq (minorsGcd C) = 1) (hsq : allR sq (sqOK j C) = true) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) : C.OkAt j p := by
  by_cases hdiv : p ∣ minorsGcd C
  · right
    obtain ⟨q, hq, hpq⟩ := stripL_cover hstrip hp h5 hdiv
    have hok := allR_spec hsq q hq
    unfold sqOK at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨hgcd, hmod⟩ := hok
    have hgcd' := Nat.eq_of_beq_eq_true hgcd
    have hq' : (q.q : ℤ) ∣ diagT C q.i - ((j * q.w * q.w : ℕ) : ℤ) :=
      Int.dvd_of_emod_eq_zero hmod
    have hp' := (Int.natCast_dvd_natCast.mpr hpq).trans hq'
    refine ⟨q.w, fun hw => ?_, ?_⟩
    · have : p ∣ Nat.gcd q.w q.q := Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hw) hpq
      rw [hgcd'] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · have e : ((j * q.w * q.w : ℕ) : ℤ) = (j : ℤ) * (q.w : ℤ) ^ 2 := by push_cast; ring
      rw [e] at hp'
      unfold diagT at hp'
      by_cases h0 : q.i = 0
      · rw [show Nat.beq q.i 0 = true from Nat.beq_eq_true_eq _ _ ▸ h0, Bool.cond_true] at hp'
        exact Or.inl hp'
      · rw [beq_false_of_ne h0, Bool.cond_false] at hp'
        by_cases h1 : q.i = 1
        · rw [show Nat.beq q.i 1 = true from Nat.beq_eq_true_eq _ _ ▸ h1, Bool.cond_true] at hp'
          exact Or.inr (Or.inl hp')
        · rw [beq_false_of_ne h1, Bool.cond_false] at hp'
          exact Or.inr (Or.inr hp')
  · left
    intro hle
    exact hdiv (dvd_minorsGcd_aux _ hle)

/-! ### A witness -/

/-- **A witness gives `L ⊇ S`.** -/
theorem rep_of_witOK (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (S : GramLattice (Fin 3)) {a b c d : ℕ} {e : ℤ} {f : ℕ} (hS : ternOf S = tern6 a b c d e f)
    {w : Wit} (h : witOK H.j H.s H.acc2 H.acc3 a b c (d, e, f) w = true) : L.Represents S := by
  unfold witOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hCa, hCδ⟩, hCD⟩, h2⟩, h3⟩, hstrip⟩, hsq⟩ := h
  simp only [witC] at hCa hCδ hCD h2 h3 hstrip hsq
  rw [← hS] at hCa hCδ hCD h2 h3 hstrip hsq
  refine hL.trans (represents_of_corr H.K hK H.s_pos S w.l₀ w.l₁ w.l₂ hCa hCδ hCD fun p hp => ?_)
  rcases prime_cases hp with rfl | rfl | h5
  · exact locOK_sound (by norm_num) H.acc2_sound h2
  · exact locOK_sound (by norm_num) H.acc3_sound h3
  · exact H.okAt_sound p hp h5 _ (okAt_of_sq (Nat.eq_of_beq_eq_true hstrip) hsq hp h5)

/-! ### The enumeration -/

theorem cdivZ_le {n e : ℤ} {m : ℕ} (hm : 0 < m) : cdivZ n m ≤ e ↔ n ≤ e * m := by
  unfold cdivZ
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  constructor
  · intro h
    have : -e ≤ (-n) / (m : ℤ) := by linarith
    have := (Int.le_ediv_iff_mul_le hm').mp this
    linarith
  · intro h
    have : -e ≤ (-n) / (m : ℤ) := (Int.le_ediv_iff_mul_le hm').mpr (by linarith)
    linarith

/-- **Membership in the enumeration.** -/
theorem mem_liftsOf {a b c U pend maxm d : ℕ} {e : ℤ} {f : ℕ} (hd : 2 * d ≤ a)
    (he₁ : eLo a b c d ≤ e) (he₂ : e ≤ eHi a b c d) (hf₁ : fLo a b c d e ≤ f)
    (hf₂ : f ≤ fHi a b c d U e) (hpt : ptOK a b c d e f pend maxm = true) :
    (d, e, f) ∈ liftsOf a b c U pend maxm := by
  unfold liftsOf
  rw [mem_natFlat]
  refine ⟨d, by omega, ?_⟩
  rw [mem_natFlat]
  refine ⟨(e - eLo a b c d).toNat, by omega, ?_⟩
  have hei : eLo a b c d + ((e - eLo a b c d).toNat : ℤ) = e := by omega
  rw [hei, mem_natFlat]
  refine ⟨f - fLo a b c d e, by omega, ?_⟩
  rw [show fLo a b c d e + (f - fLo a b c d e) = f by omega, hpt, Bool.cond_true]
  exact List.mem_singleton_self _

/-! ### A block -/

/-- The normalization of the signs of `d` and `e` used by the enumeration: `d ≥ 0`, `e ≥ 0` if
`d = 0`, and `a e ≥ b d` if `b = 0` or `2 b = a`. -/
structure Tern.Normal (g : Tern) : Prop where
  d_nonneg : 0 ≤ g.d
  e_nonneg : g.d = 0 → 0 ≤ g.e
  e_ge : g.b = 0 ∨ 2 * g.b = g.a → g.b * g.d ≤ g.a * g.e

theorem rDE_eq (a b c d : ℕ) (e : ℤ) (ha : 0 < a) (hδ : b * b < a * c) :
    (rDE a b c d e : ℤ) = (c : ℤ) * d * d - 2 * b * d * e + a * e * e := by
  unfold rDE
  have hnn : (0 : ℤ) ≤ ((c * d * d : ℕ) : ℤ) - 2 * ((b * d : ℕ) : ℤ) * e + (a : ℤ) * e * e := by
    have := quad_nonneg_natCast ha hδ d e
    push_cast; linarith
  rw [Int.toNat_of_nonneg hnn]
  push_cast; ring

theorem eLo_le {a b c d : ℕ} {e : ℤ} (ha0 : 0 < a)
    (hlo : -((a * c - b * b : ℕ) : ℤ) ≤ 2 * ((a : ℤ) * e - b * d))
    (hd0 : d = 0 → 0 ≤ e) (hbd : (b = 0 ∨ 2 * b = a) → (b : ℤ) * d ≤ a * e) :
    eLo a b c d ≤ e := by
  have h2a : 0 < 2 * a := by omega
  have hL0 : eSize a b c d ≤ e := by
    unfold eSize; rw [cdivZ_le h2a]; push_cast; linarith
  have hL1 : eSign a b c d ≤ e := by
    unfold eSign
    cases hd : Nat.beq d 0
    · exact hL0
    · exact max_le hL0 (hd0 (Nat.eq_of_beq_eq_true hd))
  unfold eLo
  cases hcnd : (Nat.beq b 0 || Nat.beq (2 * b) a)
  · exact hL1
  · refine max_le hL1 ?_
    rw [cdivZ_le ha0]
    have : b = 0 ∨ 2 * b = a := by
      simp only [Bool.or_eq_true] at hcnd
      rcases hcnd with h' | h'
      · exact Or.inl (Nat.eq_of_beq_eq_true h')
      · exact Or.inr (Nat.eq_of_beq_eq_true h')
    have := hbd this
    push_cast; linarith

theorem le_eHi {a b c d : ℕ} {e : ℤ} (ha0 : 0 < a)
    (hhi : 2 * ((a : ℤ) * e - b * d) ≤ ((a * c - b * b : ℕ) : ℤ)) : e ≤ eHi a b c d := by
  unfold eHi
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast (show 0 < 2 * a by omega))]
  push_cast; linarith

theorem fLo_le {a b c d f : ℕ} {e : ℤ} (ha0 : 0 < a) (hδ : 0 < a * c - b * b) (haf : a ≤ f)
    (hproj : a * c - b * b + d * d ≤ a * f)
    (hlow : dZero a b c + rDE a b c d e ≤ (a * c - b * b) * f) : fLo a b c d e ≤ f := by
  unfold fLo
  refine max_le haf (max_le ?_ ?_)
  · refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul ha0).mpr ?_)
    rw [show (f + 1) * a = a * f + a by ring]
    omega
  · refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hδ).mpr ?_)
    rw [show (f + 1) * (a * c - b * b) = (a * c - b * b) * f + (a * c - b * b) by ring]
    omega

theorem le_fHi {a b c d f U : ℕ} {e : ℤ} (hδ : 0 < a * c - b * b)
    (hup : (a * c - b * b) * f ≤ U + rDE a b c d e) : f ≤ fHi a b c d U e := by
  unfold fHi
  rw [Nat.le_div_iff_mul_le hδ, mul_comm]
  exact hup

/-- A maximal ternary is primitive. -/
theorem gcd_eq_one_of_max {g : Tern} (hmax : IsMaximal g.toMatrix) {a b c d f : ℕ}
    (ha : g.a = a) (hb : g.b = b) (hc : g.c = c) (hd : g.d = d) (hf : g.f = f) :
    Nat.gcd a (Nat.gcd b (Nat.gcd c (Nat.gcd d (Nat.gcd g.e.natAbs f)))) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hsym : ∀ i j, g.toMatrix i j = g.toMatrix j i := by
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  have hnz := nonzeroMod_of_isMaximal hmax hsym hp
  rw [Tern.ofMatrix_toMatrix] at hnz
  apply hnz
  simp only [Nat.dvd_gcd_iff] at hpd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpd
  rw [ha, hb, hc, hd, hf]
  exact ⟨Int.natCast_dvd_natCast.mpr h1, Int.natCast_dvd_natCast.mpr h2,
    Int.natCast_dvd_natCast.mpr h3, Int.natCast_dvd_natCast.mpr h4, Int.natCast_dvd.mpr h5,
    Int.natCast_dvd_natCast.mpr h6⟩

/-- **The terminal check of a block.** Every reduced maximal `S` with normalized signs and leading
block `(a, b, c)` is represented by `L`, given the checked tables. -/
theorem termOK_sound (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    {r2 mx mw : ℕ} (hr2 : r2OK r2 = true)
    (hmx : ∀ blk < 729, mxRowOK (tget mx 729 blk) (tget mw 3645 blk) blk = true)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) (hred : (ternOf S).IsReduced)
    (hnorm : (ternOf S).Normal) {a b c : ℕ} (ha : (ternOf S).a = a) (hb : (ternOf S).b = b)
    (hc : (ternOf S).c = c) {cert : TermCert}
    (h : termOK H.j H.s H.acc2 H.acc3 r2 mx a b c cert = true) : L.Represents S := by
  set g := ternOf S with hg
  have hmax' : IsMaximal g.toMatrix := by rw [hg, ternOf_toMatrix]; exact hmax
  set maxm := maxmOf mx a b c with hmaxm
  have hm : maxm.testBit (loc3 (r9 g.d) (r9 g.e) (r9 g.f)) = true := by
    rw [hmaxm, maxmOf, ← chunk3_eq ha hb hc]; exact mx_spec hmx g hmax'
  set opts := decOpts cert.opts with hopts_def
  set dom := domainB r2 maxm a b c with hdom_def
  have hdom : dom.testBit (classIdx g) = true := classIdx_mem_domain hr2 g hmax' ha hb hc hm
  set pend := pendB H.acc2 H.acc3 H.s a b c dom maxm opts with hpend_def
  unfold termOK termCore at h
  rw [← hmaxm, ← hdom_def, ← hopts_def, ← hpend_def] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hopts, hrest⟩ := h
  have hoptOK := allR_spec hopts
  obtain ⟨hbc, hdelta⟩ := delta_natCast S ha hb hc
  have ha0 : 0 < a := by have := a_pos S; rw [ha] at this; exact_mod_cast this
  have hD : 0 < g.det := det_pos S
  -- `D ≥ D₀`
  have hD0 : ((dZero a b c : ℕ) : ℤ) ≤ g.det := by
    have hh := hred.height
    rw [hdelta, ha] at hh
    obtain ⟨D, hDeq⟩ : ∃ D : ℕ, g.det = D := ⟨g.det.toNat, (Int.toNat_of_nonneg hD.le).symm⟩
    rw [hDeq] at hh ⊢
    set X := a * c - b * b
    have h1 : 3 * X * X ≤ 4 * (a * D) := by
      have : ((3 * X * X : ℕ) : ℤ) ≤ ((4 * (a * D) : ℕ) : ℤ) := by push_cast; nlinarith
      exact_mod_cast this
    have h4a : 0 < 4 * a := by omega
    have : dZero a b c < D + 1 := by
      rw [show dZero a b c = (3 * X * X + 4 * a - 1) / (4 * a) from rfl,
        Nat.div_lt_iff_lt_mul h4a, show (D + 1) * (4 * a) = 4 * (a * D) + 4 * a by ring]
      omega
    exact_mod_cast Nat.lt_succ_iff.mp this
  by_cases hcov0 : (coverAll H.acc2 H.acc3 H.s a b c maxm (dZero a b c) opts).testBit (classIdx g)
      = true
  · obtain ⟨o, ho, hco⟩ := coverAll_testBit hcov0
    exact rep_of_optCover H hK L hL S hmax ha hb hc hm o (hoptOK o ho) hD0 hco
  have hcov0' : (coverAll H.acc2 H.acc3 H.s a b c maxm (dZero a b c) opts).testBit (classIdx g)
      = false := by simpa using hcov0
  have hpend : pend.testBit (classIdx g) = true := by
    rw [hpend_def, pendB, Nat.testBit_xor, Nat.testBit_and, hdom, hcov0']; rfl
  have hpend0 : Nat.beq pend 0 = false :=
    beq_false_of_ne fun h0 => by rw [h0, Nat.zero_testBit] at hpend; exact Bool.false_ne_true hpend
  rw [hpend0, Bool.cond_false, Bool.and_eq_true] at hrest
  obtain ⟨hcapN, hwits⟩ := hrest
  have hcovU : (coverAll H.acc2 H.acc3 H.s a b c maxm (cert.U + 1) opts).testBit (classIdx g)
      = true := by
    have := congrArg (fun n => n.testBit (classIdx g)) (Nat.eq_of_beq_eq_true hcapN)
    simp only [Nat.testBit_and, Nat.testBit_xor, hpend, Nat.zero_testBit] at this
    cases hcu : (coverAll H.acc2 H.acc3 H.s a b c maxm (cert.U + 1) opts).testBit (classIdx g)
    · rw [hcu] at this; exact absurd this (by decide)
    · rfl
  by_cases hDU : ((cert.U + 1 : ℕ) : ℤ) ≤ g.det
  · obtain ⟨o, ho, hco⟩ := coverAll_testBit hcovU
    exact rep_of_optCover H hK L hL S hmax ha hb hc hm o (hoptOK o ho) hDU hco
  push Not at hDU
  -- **the enumerated lift**
  have hd0 := hnorm.d_nonneg
  have hf0 : 0 < g.f := by have := hred.a_le_f; rw [ha] at this; omega
  set dN := g.d.toNat with hdN
  set fN := g.f.toNat with hfN
  have hdZ : (dN : ℤ) = g.d := Int.toNat_of_nonneg hd0
  have hfZ : (fN : ℤ) = g.f := Int.toNat_of_nonneg hf0.le
  have hS : g = tern6 a b c dN g.e fN := by
    ext <;> simp [tern6, ha, hb, hc, hdZ, hfZ]
  have hR := rDE_eq a b c dN g.e ha0 hbc
  have hdet : g.det = ((a * c - b * b : ℕ) : ℤ) * fN - rDE a b c dN g.e := by
    rw [hR, ← hdelta, hdZ, hfZ]; unfold Tern.det; rw [ha, hb, hc]; ring
  have hδpos : 0 < a * c - b * b := by omega
  have hmu := hred.two_mu_le
  have hdle := hred.two_d_le
  rw [hdelta, ha, hb, ← hdZ] at hmu
  rw [ha, ← hdZ] at hdle
  set δ := a * c - b * b with hδdef
  have hlo : -(δ : ℤ) ≤ 2 * ((a : ℤ) * g.e - b * dN) := by
    have := neg_abs_le ((a : ℤ) * g.e - b * dN); linarith
  have hhi : 2 * ((a : ℤ) * g.e - b * dN) ≤ δ := by
    have := le_abs_self ((a : ℤ) * g.e - b * dN); linarith
  have hd2 : 2 * dN ≤ a := by
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ dN)] at hdle; exact_mod_cast hdle
  have hd0' : dN = 0 → 0 ≤ g.e := fun h0 => hnorm.e_nonneg (by rw [← hdZ, h0]; rfl)
  have hbd' : (b = 0 ∨ 2 * b = a) → (b : ℤ) * dN ≤ a * g.e := by
    intro h'
    have hbd : g.b = 0 ∨ 2 * g.b = g.a := by
      rcases h' with h' | h'
      · left; rw [hb, h']; rfl
      · right; rw [hb, ha, ← h']; push_cast; ring
    have := hnorm.e_ge hbd
    rwa [ha, hb, ← hdZ] at this
  have heLo := eLo_le ha0 hlo hd0' hbd'
  have heHi := le_eHi (c := c) ha0 hhi
  -- the range of `f`
  have hR' : (rDE a b c dN g.e : ℤ) = g.f * δ - g.det := by
    rw [hdet, ← hfZ]; ring
  have haf : a ≤ fN := by have := hred.a_le_f; rw [ha, ← hfZ] at this; exact_mod_cast this
  have hproj : δ + dN * dN ≤ a * fN := by
    have := hred.delta_le_proj
    rw [hdelta, ha, ← hfZ, ← hdZ] at this
    have : ((δ + dN * dN : ℕ) : ℤ) ≤ ((a * fN : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hlowD : dZero a b c + rDE a b c dN g.e ≤ δ * fN := by
    have : ((dZero a b c + rDE a b c dN g.e : ℕ) : ℤ) ≤ ((δ * fN : ℕ) : ℤ) := by
      push_cast; rw [hR', hfZ]; linarith
    exact_mod_cast this
  have hupD : δ * fN ≤ cert.U + rDE a b c dN g.e := by
    have : ((δ * fN : ℕ) : ℤ) ≤ ((cert.U + rDE a b c dN g.e : ℕ) : ℤ) := by
      push_cast; rw [hR', hfZ]; push_cast at hDU; linarith
    exact_mod_cast this
  have hfLo := fLo_le ha0 hδpos haf hproj hlowD
  have hfHi := le_fHi hδpos hupD
  -- the point passes `ptOK`
  have hpt : ptOK a b c dN g.e fN pend maxm = true := by
    unfold ptOK
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : 128 * (9 * (dN % 3) + 3 * rp 3 g.e + fN % 3) +
          loc2 (dN % 4) (r4 g.e) (fN % 8) = classIdx g := by
        unfold classIdx
        rw [← hdZ, ← hfZ, rp_natCast, rp_natCast, r4_natCast, r8_natCast]
      rw [this]; exact hpend
    · rw [← r9_natCast, ← r9_natCast, hdZ, hfZ]; exact hm
    · rw [gcd_eq_one_of_max hmax' ha hb hc hdZ.symm hfZ.symm]; rfl
  have hmem := mem_liftsOf hd2 heLo heHi hfLo hfHi hpt
  unfold idxAll at hwits
  obtain ⟨k, hk⟩ := idxAll_spec _ 0 hwits _ hmem
  exact rep_of_witOK H hK L hL S hS hk

end KimKimOh

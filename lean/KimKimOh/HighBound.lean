import KimKimOh.Choice
import KimKimOh.Tables.Profiles2
import Mathlib.Tactic.NormNum.Prime
import KimKimOh.Compute.HighBound

/-!
# The bounds `H_j(a, t)` (`sec:high`, `app:prescriptions`)

The profiles at 2 and 3 (`Tables.Profiles3`, `Tables.Profiles2`) give, for a maximal ternary,
a *local case*: a pair `(P₂, P₃)` of profiles for the classes of `a` modulo 4 and modulo 3
(`exists_localCase`). Each `x ∈ {0, 1, 2, 3, 6}` and options at `x mod 2` and `x mod 3` give
steps `h, d ∣ 6` carrying the local progressions (`optsOf`). An option is *valid* if `s x² < a` and,
for `x = 0`, the signed divisors of 6 pass the extra condition at the primes from 5
dividing `a` (`sdivOK`, a finite test on `a`, `h` and the residues of `c`).

`eq:scalar-cost` for an option reads `δ > thr`, with `thr = ⌊s a a₀ N / (12 (a₀ - s x²))⌋`,
`N = 3W² + 4 d² g_t²`; here `a₀ = a` when `a < 73`, and for `a ≥ 73` the least
representative `a₀ ∈ [73, 84]` of `a mod 12` (the factor `a / (a - s x²)` of the bound for `β` is
nonincreasing in `a`; the threshold keeps its other factor `a`). `high a a₀ t` is
the largest over the local cases of the least `thr` over the valid options, so `δ > high`
gives a valid option satisfying `eq:scalar-cost` for the actual case
(`represents_of_high_lt`).
For `t ≥ 27` every valid option works (`represents_of_tail`).
-/

namespace KimKimOh

open GramLattice Tables

/-! ### Local cases -/

/-- The data of a host `K` with scale `s` and determinant `j` used by §4.1. -/
structure HostSpec where
  κ : Type
  [fκ : Fintype κ]
  K : GramLattice κ
  j : ℕ
  s : ℕ
  hs : s = 1 ∨ s = 2
  acc2 : BT ℕ
  acc3 : BT ℕ
  prof2 : ℕ → List (List (List (ℕ × ℕ)))
  prof3 : ℕ → List (List (List (ℕ × ℕ)))
  pm2 : ℕ
  pm3 : ℕ
  wt2 : ℕ
  wt3 : ℕ
  ok2 : ∀ blk < 256, profChunkOK2 acc2 s prof2 pm2 wt2 blk = true
  ok3 : ∀ blk < 729, profChunkOK3 acc3 s prof3 pm3 wt3 blk = true
  acc2_sound : ∀ g : Tern, accepted2 acc2 g = true → LocallyRepresents K.gram g.toMatrix 2
  acc3_sound : ∀ g : Tern, accepted3 acc3 g = true → LocallyRepresents K.gram g.toMatrix 3
  okAt_sound : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ C : Tern, C.OkAt j p →
    LocallyRepresents K.gram C.toMatrix p

attribute [instance] HostSpec.fκ

theorem HostSpec.s_pos (H : HostSpec) : (0 : ℤ) < H.s := by
  rcases H.hs with h | h <;> rw [h] <;> norm_num

/-- The global part of `lem:functional` for the host: a ternary represented by `K` at every prime
is represented by `K`. -/
abbrev HostSpec.LocalGlobal (H : HostSpec) : Prop :=
  ∀ T : GramLattice (Fin 3), (∀ p : ℕ, p.Prime → LocallyRepresents H.K.gram T.gram p) →
    H.K.Represents T

/-- The target `L` contains `K ⊥ ⟨s⟩`. -/
abbrev HostSpec.Target (H : HostSpec) {ι : Type*} [Fintype ι] (L : GramLattice ι) : Prop :=
  L.Represents (H.K.orthSum (line H.s H.s_pos))

/-- **The local case of a maximal ternary**: profiles at 2 and 3 whose options carry the local
progressions of `sec:high`. -/
theorem exists_localCase (H : HostSpec) (g : Tern) (hmax : IsMaximal g.toMatrix) :
    ∃ P₂ ∈ maskedProfs (H.prof2 (r8 g.a % 4)) (mget H.pm2 (chunk2 g)),
      ∃ P₃ ∈ maskedProfs (H.prof3 (rp 3 g.a)) (mget H.pm3 (chunk3 g)), ∀ x : ℤ,
      ∀ o₂ ∈ P₂.getD (rp 2 x) [], ∀ o₃ ∈ P₃.getD (rp 3 x) [], ∃ y₀ : ℤ,
        LocalProgressions H.K g H.s x ((normOpt 2 o₂).1 * (normOpt 3 o₃).1)
          ((normOpt 2 o₂).2 * (normOpt 3 o₃).2) y₀ := by
  obtain ⟨P₂, hP₂, h₂⟩ := (chunk2_spec H.acc2 H.s H.prof2 H.pm2 H.wt2 H.ok2 g hmax).1
  obtain ⟨P₃, hP₃, h₃⟩ := (chunk3_spec H.acc3 H.s H.prof3 H.pm3 H.wt3 H.ok3 g hmax).1
  refine ⟨P₂, hP₂, P₃, hP₃, fun x o₂ ho₂ o₃ ho₃ => ?_⟩
  obtain ⟨y₀, hy⟩ := optHolds_crt (h₂ x o₂ ho₂) (h₃ x o₃ ho₃) (normOpt_two o₂).1
    (normOpt_two o₂).2 (normOpt_three o₃).1 (normOpt_three o₃).2
  exact ⟨y₀, fun y hy' => by
    obtain ⟨k₀, hk⟩ := hy y hy'
    exact ⟨k₀, fun k hk' => ⟨H.acc2_sound _ (hk k hk').1, H.acc3_sound _ (hk k hk').2⟩⟩⟩

/-! ### The signed divisors of 6 when `x = 0` -/

theorem mem_bigPrimes72 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h72 : p ≤ 72) : p ∈ bigPrimes72 := by
  interval_cases p <;> first | (simp [bigPrimes72]; done) | (exfalso; norm_num at hp)

theorem sdivOK_spec {j s a h : ℕ} (hok : sdivOK j s a h = true) (ha : 0 < a) (ha73 : a < 73)
    (hh : 0 < h) (y₀ c : ℤ) :
    ∃ y : ℤ, (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 6 ∨ y = -1 ∨ y = -2 ∨ y = -3 ∨ y = -6) ∧
      (h : ℤ) ∣ y - y₀ ∧ ∀ p : ℕ, p.Prime → 5 ≤ p → (p : ℤ) ∣ a → ¬ (p : ℤ) ∣ c →
        (p : ℤ) ∣ c - s * y * y ∨ ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (p : ℤ) ∣ (c - s * y * y) - j * u ^ 2 := by
  set Pr := (primesOf a).prod with hPr
  have hmemP : ∀ p ∈ primesOf a, 0 < p := by
    intro p hp
    simp only [primesOf, List.mem_filter] at hp
    have : ∀ q ∈ bigPrimes72, 0 < q := by decide
    exact this p hp.1
  have hPrpos : 0 < Pr := List.prod_pos hmemP
  set c' : ℕ := (c % Pr).toNat with hc'
  have hc'lt : c' < Pr := by
    have := Int.emod_lt_of_pos c (show (0 : ℤ) < Pr by exact_mod_cast hPrpos); omega
  have hc'eq : (c' : ℤ) = c % Pr := by
    have := Int.emod_nonneg c (show (Pr : ℤ) ≠ 0 by exact_mod_cast hPrpos.ne'); omega
  set st : ℕ := (y₀ % h).toNat with hst
  have hstlt : st < h := by
    have := Int.emod_lt_of_pos y₀ (show (0 : ℤ) < h by exact_mod_cast hh); omega
  have hsteq : (st : ℤ) = y₀ % h := by
    have := Int.emod_nonneg y₀ (show (h : ℤ) ≠ 0 by exact_mod_cast hh.ne'); omega
  unfold sdivOK at hok
  rw [List.all_eq_true] at hok
  have h1 := hok c' (List.mem_range.mpr hc'lt)
  rw [List.all_eq_true] at h1
  have h2 := h1 st (List.mem_range.mpr hstlt)
  rw [List.any_eq_true] at h2
  obtain ⟨y, hy6, hy⟩ := h2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hy
  obtain ⟨hyh, hyp⟩ := hy
  refine ⟨y, ?_, ?_, fun p hp h5 hpa hpc => ?_⟩
  · simpa [sdiv6] using hy6
  · have e1 : (h : ℤ) ∣ y - st := Int.dvd_of_emod_eq_zero hyh
    have e2 : (h : ℤ) ∣ (st : ℤ) - y₀ := by
      rw [hsteq]; exact ⟨-(y₀ / h), by have := Int.emod_add_mul_ediv y₀ h; linarith⟩
    have := dvd_add e1 e2
    rwa [show y - st + (st - y₀) = y - y₀ by ring] at this
  · -- `p` is one of the primes of `a`
    have hpa' : p ∣ a := Int.natCast_dvd_natCast.mp hpa
    have hp72 : p ≤ 72 := (Nat.le_of_dvd ha hpa').trans (by omega)
    have hpm : p ∈ primesOf a := by
      simp only [primesOf, List.mem_filter, beq_iff_eq]
      exact ⟨mem_bigPrimes72 hp h5 hp72, Nat.mod_eq_zero_of_dvd hpa'⟩
    have hpPr : (p : ℤ) ∣ Pr := by exact_mod_cast List.dvd_prod hpm
    -- `c' ≡ c (mod p)`
    have hcc : (p : ℤ) ∣ c - c' := by
      rw [hc'eq]
      have e : c - c % Pr = Pr * (c / Pr) := by have := Int.emod_add_mul_ediv c Pr; linarith
      rw [e]
      exact dvd_mul_of_dvd_left hpPr _
    rcases (Bool.or_eq_true _ _).mp (hyp p hpm) with hc0 | hsq
    · exfalso
      apply hpc
      have : (p : ℤ) ∣ (c' : ℤ) := Int.dvd_of_emod_eq_zero (by simpa using hc0)
      have := dvd_add hcc this
      rwa [sub_add_cancel] at this
    · unfold sqClassOK at hsq
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
        bne_iff_ne, ne_eq, List.mem_range] at hsq
      rcases hsq with h0 | ⟨u, hu, hu0, hu1⟩
      · left
        have h0' : (p : ℤ) ∣ (c' : ℤ) - s * y * y := Int.dvd_of_emod_eq_zero h0
        have := dvd_add hcc h0'
        rwa [show c - c' + (c' - s * y * y) = c - s * y * y by ring] at this
      · right
        refine ⟨u, fun hdvd => hu0 ?_, ?_⟩
        · have := Int.le_of_dvd (by omega) hdvd
          have : (u : ℤ) < p := by exact_mod_cast hu
          have hu' : (0 : ℤ) < u := by exact_mod_cast Nat.pos_of_ne_zero hu0
          omega
        · have h1' : (p : ℤ) ∣ ((c' : ℤ) - s * y * y) - j * u * u := Int.dvd_of_emod_eq_zero hu1
          have := dvd_add hcc h1'
          rw [show c - c' + ((c' : ℤ) - s * y * y - j * u * u) = (c - s * y * y) - j * u ^ 2 by
            ring] at this
          exact this

/-! ### Options, thresholds and `high` -/

theorem foldl_min_mem : ∀ (l : List ℕ) (x : ℕ), l.foldl min x ∈ x :: l
  | [], x => by simp
  | y :: l, x => by
    have := foldl_min_mem l (min x y)
    simp only [List.foldl_cons]
    rcases min_choice x y with h | h <;> rw [h] at this ⊢ <;>
      simp only [List.mem_cons] at this ⊢ <;> tauto

theorem minL_mem {l : List ℕ} (hl : l ≠ []) : minL l ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x l => exact foldl_min_mem l x

theorem minL_le : ∀ {l : List ℕ} {v : ℕ}, v ∈ l → minL l ≤ v
  | [], _, h => by simp at h
  | x :: l, v, h => by
    unfold minL
    have key : ∀ (l : List ℕ) (m : ℕ), l.foldl min m ≤ m ∧ ∀ w ∈ l, l.foldl min m ≤ w := by
      intro l
      induction l with
      | nil => intro m; simp
      | cons y l ih =>
        intro m
        obtain ⟨h1, h2⟩ := ih (min m y)
        refine ⟨h1.trans (min_le_left _ _), fun w hw => ?_⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h1.trans (min_le_right _ _)
        · exact h2 w hw
    rcases List.mem_cons.mp h with rfl | h
    · exact (key l v).1
    · exact (key l x).2 v h

theorem le_foldl_max {β : Type*} (f : β → ℕ) :
    ∀ (l : List β) (m : ℕ), m ≤ l.foldl (fun m pr => max m (f pr)) m ∧
      ∀ pr ∈ l, f pr ≤ l.foldl (fun m pr => max m (f pr)) m
  | [], m => by simp
  | y :: l, m => by
    obtain ⟨h1, h2⟩ := le_foldl_max f l (max m (f y))
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨(le_max_left _ _).trans h1, fun pr hpr => ?_⟩
    rcases hpr with rfl | hpr
    · exact (le_max_right _ _).trans h1
    · exact h2 pr hpr

theorem foldl_max_le {β : Type*} (f : β → ℕ) {B : ℕ} :
    ∀ (l : List β) (m : ℕ), m ≤ B → (∀ pr ∈ l, f pr ≤ B) →
      l.foldl (fun m pr => max m (f pr)) m ≤ B
  | [], m, hm, _ => hm
  | y :: l, m, hm, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le f l _ (max_le hm (hl y (by simp))) (fun pr hpr => hl pr (by simp [hpr]))

theorem foldl_max_lt {β : Type*} (f : β → ℕ) {δ : ℕ} (l : List β) (m : ℕ) (hm : m < δ)
    (hl : ∀ pr ∈ l, f pr < δ) : l.foldl (fun m pr => max m (f pr)) m < δ := by
  have := foldl_max_le f (B := δ - 1) l m (by omega) fun pr hpr => by have := hl pr hpr; omega
  omega

theorem validOpts_ne_nil {j s : ℕ} {L₂ L₃ : List (List (List (ℕ × ℕ)))} {a₀ : ℕ}
    (hok : pairsOK j s L₂ L₃ a₀ = true) {P₂ P₃ : List (List (ℕ × ℕ))}
    (hP : (P₂, P₃) ∈ pairsOf L₂ L₃) : validOpts j s a₀ P₂ P₃ ≠ [] := by
  unfold pairsOK at hok
  rw [List.all_eq_true] at hok
  simpa [List.isEmpty_iff] using hok _ hP

/-- From `δ > high`: every local case has a valid option with threshold below `δ`. -/
theorem exists_opt_of_high {j s : ℕ} {L₂ L₃ : List (List (List (ℕ × ℕ)))}
    {a a₀ t δ : ℕ} (hok : pairsOK j s L₂ L₃ a₀ = true)
    (hδ : high j s L₂ L₃ a a₀ t < δ) {P₂ P₃ : List (List (ℕ × ℕ))}
    (hP : (P₂, P₃) ∈ pairsOf L₂ L₃) :
    ∃ o ∈ validOpts j s a₀ P₂ P₃, thr s a a₀ (Windows.gWin t) o < δ := by
  have hne := validOpts_ne_nil hok hP
  have hle := (le_foldl_max (fun pr : List (List (ℕ × ℕ)) × List (List (ℕ × ℕ)) =>
    minL ((validOpts j s a₀ pr.1 pr.2).map (thr s a a₀ (Windows.gWin t))))
    (pairsOf L₂ L₃) 0).2 _ hP
  have hmem := minL_mem (l := (validOpts j s a₀ P₂ P₃).map (thr s a a₀ (Windows.gWin t)))
    (by simpa using hne)
  obtain ⟨o, ho, hoeq⟩ := List.mem_map.mp hmem
  exact ⟨o, ho, by unfold high at hδ; simp only at hle; omega⟩

theorem mem_optsOf {a₀ : ℕ} {P₂ P₃ : List (List (ℕ × ℕ))} {o : ℕ × ℕ × ℕ}
    (h : o ∈ optsOf a₀ P₂ P₃) :
    ∃ x ∈ xList, (x ≠ 0 ∨ a₀ < 73) ∧ ∃ o₂ ∈ P₂.getD (x % 2) [], ∃ o₃ ∈ P₃.getD (x % 3) [],
      o = (x, (normOpt 2 o₂).1 * (normOpt 3 o₃).1, (normOpt 2 o₂).2 * (normOpt 3 o₃).2) := by
  unfold optsOf at h
  rw [List.mem_flatMap] at h
  obtain ⟨x, hx, ho⟩ := h
  split_ifs at ho with hc
  · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
    rw [List.mem_flatMap] at ho
    obtain ⟨o₂, ho₂, ho⟩ := ho
    obtain ⟨o₃, ho₃, rfl⟩ := List.mem_map.mp ho
    exact ⟨x, hx, hc, o₂, ho₂, o₃, ho₃, rfl⟩
  · simp at ho

theorem steps_of_normOpt (o₂ o₃ : ℕ × ℕ) :
    let h := (normOpt 2 o₂).1 * (normOpt 3 o₃).1
    let d := (normOpt 2 o₂).2 * (normOpt 3 o₃).2
    (h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 6) ∧ (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6) := by
  have e2 : ∀ u, u ∣ 2 → u = 1 ∨ u = 2 := fun u hu => by
    have := Nat.le_of_dvd (by norm_num) hu
    interval_cases u <;> simp_all
  have e3 : ∀ u, u ∣ 3 → u = 1 ∨ u = 3 := fun u hu => by
    have := Nat.le_of_dvd (by norm_num) hu
    interval_cases u <;> simp_all
  obtain ⟨a1, a2⟩ := normOpt_two o₂
  obtain ⟨b1, b2⟩ := normOpt_three o₃
  rcases e2 _ a1 with h1 | h1 <;> rcases e2 _ a2 with h2 | h2 <;> rcases e3 _ b1 with h3 | h3 <;>
    rcases e3 _ b2 with h4 | h4 <;> simp only [h1, h2, h3, h4] <;> norm_num

/-! ### The cover theorems -/

theorem rp_natCast (p x : ℕ) : rp p (x : ℤ) = x % p := by unfold rp; omega

/-- **`sec:high` with the bounds `H_j`.** Let `S` be maximal in a reduced basis with `a ≥ 2`
and `δ < P_{t+1}`, and let `L₂`, `L₃` contain the profiles selected for its chunks. Let `a₀ = a`
if `a < 73`, and otherwise `a₀ ∈ [73, a]`. If every local case from `L₂ × L₃` has a valid option
and `δ > high a a₀ t`, then `L` represents `S`. -/
theorem represents_of_high_lt (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) (hred : (ternOf S).IsReduced)
    (t : ℕ) (ht : (ternOf S).delta < Primes.P (t + 1)) (a₀ : ℕ)
    (ha₀ : a₀ ≤ (ternOf S).a.toNat)
    (hsmall : (ternOf S).a < 73 → a₀ = (ternOf S).a.toNat) (hbig : 73 ≤ (ternOf S).a → 73 ≤ a₀)
    (L₂ L₃ : List (List (List (ℕ × ℕ))))
    (hL₂ : ∀ P ∈ maskedProfs (H.prof2 (r8 (ternOf S).a % 4)) (mget H.pm2 (chunk2 (ternOf S))), P ∈ L₂)
    (hL₃ : ∀ P ∈ maskedProfs (H.prof3 (rp 3 (ternOf S).a)) (mget H.pm3 (chunk3 (ternOf S))), P ∈ L₃)
    (hok : pairsOK H.j H.s L₂ L₃ a₀ = true)
    (hδ : high H.j H.s L₂ L₃ (ternOf S).a.toNat a₀ t < (ternOf S).delta.toNat) :
    L.Represents S := by
  set g := ternOf S with hg
  have ha : 0 < g.a := a_pos S
  have hδpos : 0 < g.delta := delta_pos S
  set a := g.a.toNat with hadef
  have haeq : (a : ℤ) = g.a := by omega
  have hmax' : IsMaximal g.toMatrix := by rw [hg, ternOf_toMatrix]; exact hmax
  obtain ⟨P₂, hP₂, P₃, hP₃, hopt⟩ := exists_localCase H g hmax'
  have hpair : (P₂, P₃) ∈ pairsOf L₂ L₃ := by
    unfold pairsOf
    exact List.mem_flatMap.mpr ⟨P₂, hL₂ P₂ hP₂, List.mem_map.mpr ⟨P₃, hL₃ P₃ hP₃, rfl⟩⟩
  obtain ⟨o, ho, hthr⟩ := exists_opt_of_high hok hδ hpair
  rw [validOpts, List.mem_filter] at ho
  obtain ⟨ho, hval⟩ := ho
  obtain ⟨x, hx, hx0, o₂, ho₂, o₃, ho₃, rfl⟩ := mem_optsOf ho
  simp only [validOpt, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at hval
  obtain ⟨hsx, hsd⟩ := hval
  set h := (normOpt 2 o₂).1 * (normOpt 3 o₃).1 with hh
  set d := (normOpt 2 o₂).2 * (normOpt 3 o₃).2 with hd
  obtain ⟨hh6, hd6⟩ := steps_of_normOpt o₂ o₃
  obtain ⟨y₀, hprog⟩ := hopt x o₂ (by rw [rp_natCast]; exact ho₂) o₃ (by rw [rp_natCast]; exact ho₃)
  have hs0 : (0 : ℤ) < H.s := H.s_pos
  have hxl : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 6 := by simpa [xList] using hx
  set gw := Windows.gWin t with hgw
  refine represents_of_scalarCost H.K (H.j : ℤ) (s := (H.s : ℤ)) (by rcases H.hs with h' | h' <;> simp [h'])
    hs0 hK H.okAt_sound L hL S hmax hred (x : ℤ) (by rcases hxl with h' | h' | h' | h' | h' <;> simp [h'])
    h d hh6 hd6 y₀ hprog t ht (if x = 0 then 12 else (h : ℤ) * gw) (fun hx' => by
      rw [ite_eq_right_iff.mpr (fun h0 => absurd (by exact_mod_cast h0) hx')]) (fun hx' => ?_) ?_
  · -- `x = 0`: the signed divisors of 6
    have hx0' : x = 0 := by exact_mod_cast hx'
    refine ⟨by simp [hx0'], ?_⟩
    have ha73 : g.a < 73 := by
      by_contra hc
      have := hbig (by omega)
      rcases hx0 with hx0 | hx0 <;> omega
    have ha₀a := hsmall ha73
    have hsd' : sdivOK H.j H.s a₀ h = true := by
      rcases hsd with h' | h'
      · exact absurd hx0' h'
      · exact h'
    have hhpos : 0 < h := by rcases hh6 with h' | h' | h' | h' <;> omega
    obtain ⟨y, hy6, hyh, hyc⟩ := sdivOK_spec hsd' (by omega) (by omega) hhpos y₀ g.c
    refine ⟨y, hy6, hyh, fun p hp h5 hpa hpc => ?_⟩
    exact hyc p hp h5 (by rw [ha₀a, haeq]; exact hpa) hpc
  · -- `eq:scalar-cost` from the threshold
    have hden : 0 < 12 * (a₀ - H.s * x * x) := by omega
    unfold thr at hthr
    have hlt := (Nat.div_lt_iff_lt_mul hden).mp hthr
    have hsx' : H.s * x * x ≤ a₀ := hsx.le
    have hWnat : ((widthW gw (x, h, d) : ℕ) : ℤ) = if x = 0 then 12 else (h : ℤ) * gw := by
      unfold widthW
      split_ifs <;> simp
    -- cast the threshold inequality to `ℤ`
    have hZ : (H.s : ℤ) * a * a₀ * (3 * (widthW gw (x, h, d) : ℤ) ^ 2 + 4 * (d * gw : ℤ) ^ 2) <
        12 * g.delta * (a₀ - H.s * x * x) := by
      have := hlt
      have hcast : ((a₀ - H.s * x * x : ℕ) : ℤ) = a₀ - H.s * x * x := by push_cast [hsx']; ring
      have hδc : ((g.delta.toNat : ℕ) : ℤ) = g.delta := by omega
      have := (Int.ofNat_lt.mpr this)
      push_cast [hsx'] at this
      rw [hδc] at this
      simp only [widthW] at this ⊢
      linarith
    rw [hWnat] at hZ
    set N := 3 * (if x = 0 then (12 : ℤ) else (h : ℤ) * gw) ^ 2 + 4 * ((d : ℤ) * gw) ^ 2
      with hN
    have hNnn : 0 ≤ N := by positivity
    -- monotonicity in `a`
    have hmono : (a : ℤ) * (a₀ - H.s * x * x) ≤ a₀ * (a - H.s * x * x) := by
      have : (a₀ : ℤ) ≤ a := by exact_mod_cast ha₀
      nlinarith [show (0 : ℤ) ≤ H.s * x * x by positivity]
    have ha₀pos : (0 : ℤ) < a₀ := by omega
    have key : (a₀ : ℤ) * (H.s * g.a ^ 2 * N) < a₀ * (12 * g.delta * (g.a - H.s * x * x)) := by
      rw [← haeq]
      have hδ0 : (0 : ℤ) ≤ 12 * g.delta := by omega
      calc (a₀ : ℤ) * (H.s * a ^ 2 * N) = a * (H.s * a * a₀ * N) := by ring
        _ < a * (12 * g.delta * (a₀ - H.s * x * x)) := by
          have : (0 : ℤ) < a := by omega
          exact mul_lt_mul_of_pos_left hZ this
        _ = 12 * g.delta * (a * (a₀ - H.s * x * x)) := by ring
        _ ≤ 12 * g.delta * (a₀ * (a - H.s * x * x)) := mul_le_mul_of_nonneg_left hmono hδ0
        _ = a₀ * (12 * g.delta * (a - H.s * x * x)) := by ring
    have := lt_of_mul_lt_mul_left key ha₀pos.le
    convert this using 2

/-- `high < δ` once every local case has a valid option with threshold below `δ`. -/
theorem high_lt_of_exists {j s : ℕ} {L₂ L₃ : List (List (List (ℕ × ℕ)))} {a a₀ t δ : ℕ}
    (hpos : 0 < δ)
    (h : ∀ P₂ P₃, (P₂, P₃) ∈ pairsOf L₂ L₃ → ∃ o ∈ validOpts j s a₀ P₂ P₃,
      thr s a a₀ (Windows.gWin t) o < δ) :
    high j s L₂ L₃ a a₀ t < δ := by
  unfold high
  refine foldl_max_lt _ _ 0 hpos fun pr hpr => ?_
  obtain ⟨o, ho, hlt⟩ := h pr.1 pr.2 hpr
  exact (minL_le (List.mem_map.mpr ⟨o, ho, rfl⟩)).trans_lt hlt

/-- `high < δ` once every valid option has threshold below `δ`. -/
theorem high_lt {j s : ℕ} {L₂ L₃ : List (List (List (ℕ × ℕ)))} {a a₀ t δ : ℕ}
    (hpos : 0 < δ) (hok : pairsOK j s L₂ L₃ a₀ = true)
    (h : ∀ P₂ P₃, (P₂, P₃) ∈ pairsOf L₂ L₃ → ∀ o ∈ validOpts j s a₀ P₂ P₃,
      thr s a a₀ (Windows.gWin t) o < δ) :
    high j s L₂ L₃ a a₀ t < δ :=
  high_lt_of_exists hpos fun P₂ P₃ hP => by
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (validOpts_ne_nil hok hP)
    exact ⟨o, ho, h P₂ P₃ hP o ho⟩

theorem three_a_sq_le {g : Tern} (hred : g.IsReduced) : 3 * g.a ^ 2 ≤ 4 * g.delta := by
  have := hred.b_nonneg; have := hred.two_b_le_a; have := hred.a_le_c
  unfold Tern.delta
  nlinarith

/-- **The tail `t ≥ 27`** (`app:prescriptions`): every valid option satisfies `eq:scalar-cost`,
since `h, d ≤ 6`, `W ≤ 6 g_t`, `s x² ≤ 72` and `3 P_t > 4 (3066 g_t²)²` (`tail_ineq`). -/
theorem represents_of_tail (H : HostSpec)
    (hK : H.LocalGlobal) {ι : Type*} [Fintype ι] (L : GramLattice ι)
    (hL : H.Target L)
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) (hred : (ternOf S).IsReduced)
    (t : ℕ) (ht27 : 27 ≤ t) (htP : Primes.P t ≤ (ternOf S).delta)
    (ht : (ternOf S).delta < Primes.P (t + 1)) (a₀ : ℕ)
    (ha₀ : a₀ ≤ (ternOf S).a.toNat)
    (hsmall : (ternOf S).a < 73 → a₀ = (ternOf S).a.toNat) (hbig : 73 ≤ (ternOf S).a → 73 ≤ a₀)
    (L₂ L₃ : List (List (List (ℕ × ℕ))))
    (hL₂ : ∀ P ∈ maskedProfs (H.prof2 (r8 (ternOf S).a % 4)) (mget H.pm2 (chunk2 (ternOf S))), P ∈ L₂)
    (hL₃ : ∀ P ∈ maskedProfs (H.prof3 (rp 3 (ternOf S).a)) (mget H.pm3 (chunk3 (ternOf S))), P ∈ L₃)
    (hok : pairsOK H.j H.s L₂ L₃ a₀ = true) :
    L.Represents S := by
  set g := ternOf S with hg
  have ha : 0 < g.a := a_pos S
  have hδpos : 0 < g.delta := delta_pos S
  have h3a := three_a_sq_le hred
  set gw := Windows.gWin t with hgw
  have hgw2 : 2 ≤ gw := by
    rw [hgw, Windows.gWin_tail ht27]
    have : 1 ≤ 2 ^ (t - 2) := Nat.one_le_two_pow
    nlinarith
  have htP' : ((Primes.P t : ℕ) : ℤ) ≤ g.delta := htP
  have htail := Windows.tail_ineq ht27
  rw [← hgw] at htail
  -- `3066 a g² < δ`
  have hbig' : (3066 * gw ^ 2 : ℤ) * g.a < g.delta := by
    by_contra hc
    push Not at hc
    set M : ℤ := 3066 * gw ^ 2
    have hM : 4 * M ^ 2 < 3 * g.delta := by
      have : ((4 * (3066 * gw ^ 2) ^ 2 : ℕ) : ℤ) < ((3 * Primes.P t : ℕ) : ℤ) := by
        exact_mod_cast htail
      push_cast at this
      linarith
    have hM0 : 0 ≤ M := by positivity
    have h1 : g.delta * g.delta ≤ (M * g.a) * (M * g.a) :=
      mul_le_mul hc hc hδpos.le (by positivity)
    nlinarith
  refine represents_of_high_lt H hK L hL S hmax hred t ht a₀ ha₀ hsmall hbig L₂ L₃ hL₂ hL₃ hok
    (high_lt (by have : 0 < (ternOf S).delta := delta_pos S; omega) hok fun P₂ P₃ _ o ho => ?_)
  rw [validOpts, List.mem_filter] at ho
  obtain ⟨ho, hval⟩ := ho
  obtain ⟨x, hx, -, o₂, -, o₃, -, rfl⟩ := mem_optsOf ho
  simp only [validOpt, Bool.and_eq_true, decide_eq_true_eq] at hval
  have hsx := hval.1
  obtain ⟨hh6, hd6⟩ := steps_of_normOpt o₂ o₃
  set h := (normOpt 2 o₂).1 * (normOpt 3 o₃).1
  set d := (normOpt 2 o₂).2 * (normOpt 3 o₃).2
  have hx6 : x ≤ 6 := by simp [xList] at hx; omega
  have hs2 : H.s ≤ 2 := by rcases H.hs with h' | h' <;> omega
  have hh6' : h ≤ 6 := by omega
  have hd6' : d ≤ 6 := by omega
  have hsx72 : H.s * x * x ≤ 72 := by
    have : x * x ≤ 36 := Nat.mul_le_mul hx6 hx6
    calc H.s * x * x = H.s * (x * x) := by ring
      _ ≤ 2 * 36 := Nat.mul_le_mul hs2 this
  have hW : widthW gw (x, h, d) ≤ 6 * gw := by
    unfold widthW; split_ifs
    · omega
    · exact Nat.mul_le_mul_right _ hh6'
  have hden : 0 < 12 * (a₀ - H.s * x * x) := by omega
  unfold thr
  rw [Nat.div_lt_iff_lt_mul hden]
  -- the numerator bound, in `ℤ`
  set W := widthW gw (x, h, d)
  have hN : 3 * W ^ 2 + 4 * (d * gw) ^ 2 ≤ 252 * gw ^ 2 := by
    have : W ^ 2 ≤ (6 * gw) ^ 2 := Nat.pow_le_pow_left hW 2
    have : (d * gw) ^ 2 ≤ (6 * gw) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hd6') 2
    nlinarith
  have h73 : a₀ ≤ 73 * (a₀ - H.s * x * x) := by omega
  set a := g.a.toNat with hadef
  have haeq : (a : ℤ) = g.a := by omega
  have hδeq : ((g.delta.toNat : ℕ) : ℤ) = g.delta := by omega
  have hbigN : 3066 * gw ^ 2 * a < g.delta.toNat := by
    have : ((3066 * gw ^ 2 * a : ℕ) : ℤ) < g.delta := by push_cast; rw [haeq]; exact hbig'
    omega
  calc H.s * a * a₀ * (3 * W ^ 2 + 4 * (d * gw) ^ 2)
      ≤ 2 * a * a₀ * (252 * gw ^ 2) := by
        apply Nat.mul_le_mul _ hN
        exact Nat.mul_le_mul (Nat.mul_le_mul hs2 le_rfl) le_rfl
    _ ≤ 2 * a * (73 * (a₀ - H.s * x * x)) * (252 * gw ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl h73) le_rfl
    _ = 12 * (a₀ - H.s * x * x) * (3066 * gw ^ 2 * a) := by ring
    _ < 12 * (a₀ - H.s * x * x) * g.delta.toNat := Nat.mul_lt_mul_of_pos_left hbigN hden
    _ = g.delta.toNat * (12 * (a₀ - H.s * x * x)) := Nat.mul_comm _ _

end KimKimOh

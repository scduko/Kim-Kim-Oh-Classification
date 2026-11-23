import KimKimOh.Primes
import KimKimOh.ExcludedClasses
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Rify
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import KimKimOh.Compute.Windows

/-!
# Sieve windows for arithmetic progressions (`sec:high`, `app:prescriptions`)

Consider `g` consecutive terms `k₀ + m i`, `i < g`, of an arithmetic progression whose step `m`
is prime to every prime of a finite set `P`, where each `p ∈ P` forbids at most `ν p` residue
classes.

* `ap_sieve`: if `Σ_p ν p ⌈g / p⌉ < g`, some term is forbidden by no prime.
* `ie_bound`: with one forbidden class at each of the distinct primes of `P`, inclusion–exclusion
  counts the survivors as `g ∏_{p ∈ P} (1 - 1/p)` with error at most `2^{|P|} - 1`, by
  induction on `P`: the terms in one class modulo `p` form a progression of step `m p` and length
  within one of `g / p`.
-/

namespace KimKimOh.Windows

open Finset Excluded Primes

/-- At most `⌈g / p⌉` of the integers `i < g` lie in a given class modulo `p`. -/
theorem card_class_le (p g ρ : ℕ) (hp : 0 < p) :
    ((range g).filter (fun i => i % p = ρ)).card ≤ (g + p - 1) / p := by
  calc ((range g).filter (fun i => i % p = ρ)).card
      ≤ (range ((g + p - 1) / p)).card := by
        refine card_le_card_of_injOn (fun i => i / p) (fun i hi => ?_) (fun i hi j hj hij => ?_)
        · simp only [coe_filter, Set.mem_ofPred_eq, mem_range, coe_range, Set.mem_Iio] at hi ⊢
          rw [Nat.div_lt_iff_lt_mul hp]
          have h1 := Nat.div_add_mod (g + p - 1) p
          have h2 := Nat.mod_lt (g + p - 1) hp
          rw [mul_comm] at h1
          omega
        · simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hi hj
          have e1 := Nat.div_add_mod i p
          have e2 := Nat.div_add_mod j p
          simp only at hij
          rw [hij, hi.2] at e1
          rw [hj.2] at e2
          omega
    _ = (g + p - 1) / p := card_range _

/-- A prime not dividing `m` divides `m (u - v)` only if it divides `u - v`. -/
theorem dvd_sub_of_dvd_mul {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) {u v : ℤ}
    (h : (p : ℤ) ∣ (m : ℤ) * (u - v)) : (p : ℤ) ∣ u - v :=
  (Int.Prime.dvd_mul' hp h).resolve_left (by exact_mod_cast hm)

/-- On a progression of step `m` with `p ∤ m`, at most `ν` residues `ρ < p` give a forbidden term. -/
theorem card_bad_res_le {p ν m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) {bad : ℤ → Prop}
    [DecidablePred bad] (hν : AtMostClasses p ν bad) (k₀ : ℤ) :
    ((range p).filter fun ρ : ℕ => bad (k₀ + m * ρ)).card ≤ ν := by
  have h' : AtMostClasses p ν (fun k => bad (k₀ + m * k)) := by
    intro ks hlen hpair
    obtain ⟨k, hk, hb⟩ := hν (ks.map fun k => k₀ + m * k) (by simp [hlen]) (by
      rw [List.pairwise_map]
      refine hpair.imp fun {u v} h hd => h ?_
      exact dvd_sub_of_dvd_mul hp hm (by convert hd using 1; ring))
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hk
    exact ⟨u, hu, hb⟩
  simpa using card_badResidues_le h' 0

/-- **The sieve on a progression.** If `Σ_{p ∈ P} ν_p ⌈g / p⌉ < g`, then some term `k₀ + m i`,
`i < g`, is forbidden by no prime of `P`. -/
theorem ap_sieve (k₀ : ℤ) (m g : ℕ) (P : Finset ℕ) (ν : ℕ → ℕ) (bad : ℕ → ℤ → Prop)
    [∀ p, DecidablePred (bad p)]
    (hP : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ m ∧ Periodic p (bad p) ∧ AtMostClasses p (ν p) (bad p))
    (hcount : ∑ p ∈ P, ν p * ((g + p - 1) / p) < g) :
    ∃ i < g, ∀ p ∈ P, ¬ bad p (k₀ + m * i) := by
  classical
  set B : ℕ → Finset ℕ := fun p => (range g).filter fun i => bad p (k₀ + m * i) with hBdef
  have hB : ∀ p ∈ P, (B p).card ≤ ν p * ((g + p - 1) / p) := by
    intro p hpP
    obtain ⟨hp, hm, hper, hν⟩ := hP p hpP
    set R := (range p).filter fun ρ : ℕ => bad p (k₀ + m * ρ)
    have hsub : B p ⊆ R.biUnion fun ρ => (range g).filter fun i => i % p = ρ := by
      intro i hi
      simp only [hBdef, mem_filter, mem_range] at hi
      refine mem_biUnion.mpr ⟨i % p, ?_, ?_⟩
      · refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hp.pos), ?_⟩
        refine (hper _ _ ⟨((m * (i / p) : ℕ) : ℤ), ?_⟩).mp hi.2
        have e : ((i : ℕ) : ℤ) = ((i % p : ℕ) : ℤ) + p * ((i / p : ℕ) : ℤ) := by
          exact_mod_cast (Nat.mod_add_div i p).symm
        rw [e, Nat.cast_mul]; ring
      · simp [hi.1]
    calc (B p).card ≤ (R.biUnion fun ρ => (range g).filter fun i => i % p = ρ).card :=
          card_le_card hsub
      _ ≤ ∑ ρ ∈ R, ((range g).filter fun i => i % p = ρ).card := card_biUnion_le
      _ ≤ ∑ _ρ ∈ R, (g + p - 1) / p := sum_le_sum fun ρ _ => card_class_le p g ρ hp.pos
      _ = R.card * ((g + p - 1) / p) := by rw [sum_const, smul_eq_mul]
      _ ≤ ν p * ((g + p - 1) / p) := Nat.mul_le_mul_right _ (card_bad_res_le hp hm hν k₀)
  obtain ⟨i, hi, hni⟩ := exists_mem_notMem_of_card_lt_card (s := P.biUnion B) (t := range g) (by
    rw [card_range]
    exact (card_biUnion_le.trans (sum_le_sum hB)).trans_lt hcount)
  refine ⟨i, mem_range.mp hi, fun p hp hb => hni (mem_biUnion.mpr ⟨p, hp, ?_⟩)⟩
  simp only [hBdef, mem_filter]
  exact ⟨hi, hb⟩

/-! ### Inclusion–exclusion -/

/-- The survivors among `k₀ + m i`, `i < g`, when each `p ∈ P` forbids the class of `c p`. -/
def surv (P : Finset ℕ) (c : ℕ → ℤ) (k₀ : ℤ) (m g : ℕ) : ℕ :=
  ((range g).filter fun i : ℕ => ∀ p ∈ P, ¬ (p : ℤ) ∣ k₀ + m * i - c p).card

/-- A class modulo `p ∤ m` meets the progression `k₀ + m i` at some `i₀ < p`. -/
theorem exists_start {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (k₀ c : ℤ) :
    ∃ i₀ < p, (p : ℤ) ∣ k₀ + m * i₀ - c := by
  have : Fact p.Prime := ⟨hp⟩
  have hm' : (m : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hm
  set z : ZMod p := (c - k₀ : ℤ) * (m : ZMod p)⁻¹
  refine ⟨z.val, ZMod.val_lt z, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id, show (z : ZMod p) = (c - k₀ : ℤ) * (m : ZMod p)⁻¹ from rfl,
    mul_comm (m : ZMod p), mul_assoc, inv_mul_cancel₀ hm']
  push_cast; ring

/-- `i₀ + p j < g` exactly for `j < ⌈(g - i₀) / p⌉`, when `i₀ < p`. -/
theorem lt_iff_lt_div {p i₀ g j : ℕ} (hp : 0 < p) (hi : i₀ < p) :
    i₀ + p * j < g ↔ j < (g + p - 1 - i₀) / p := by
  have key : j < (g + p - 1 - i₀) / p ↔ (j + 1) * p ≤ g + p - 1 - i₀ := by
    rw [← Nat.le_div_iff_mul_le hp]; omega
  rw [key, add_mul, one_mul, mul_comm j p]
  omega

/-- **One step of inclusion–exclusion.** -/
theorem surv_insert {P : Finset ℕ} {p : ℕ} (hp : p.Prime) (c : ℕ → ℤ) (k₀ : ℤ)
    {m : ℕ} (hm : ¬ p ∣ m) (g : ℕ) {i₀ : ℕ} (hi₀ : i₀ < p) (hc : (p : ℤ) ∣ k₀ + m * i₀ - c p) :
    surv P c k₀ m g =
      surv (insert p P) c k₀ m g + surv P c (k₀ + m * i₀) (m * p) ((g + p - 1 - i₀) / p) := by
  classical
  set S := (range g).filter fun i : ℕ => ∀ q ∈ P, ¬ (q : ℤ) ∣ k₀ + m * i - c q with hS
  have hsplit := card_filter_add_card_filter_not
    (s := S) (fun i : ℕ => ¬ (p : ℤ) ∣ k₀ + m * i - c p)
  -- the class of `c p` modulo `p` is the class of `i₀`
  have hclass : ∀ i : ℕ, (p : ℤ) ∣ k₀ + m * i - c p → i % p = i₀ := by
    intro i hpc
    have h1 : (p : ℤ) ∣ (m : ℤ) * ((i : ℤ) - i₀) := by
      have := dvd_sub hpc hc; convert this using 1; ring
    have h2 := dvd_sub_of_dvd_mul hp hm h1
    have h4 : ((i % p : ℕ) : ℤ) = (i₀ : ℤ) := by
      rw [Int.natCast_mod]
      have : (i : ℤ) % p = (i₀ : ℤ) % p := (Int.modEq_iff_dvd.mpr h2).symm
      rw [this]; exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hi₀)
    exact_mod_cast h4
  have e1 : S.filter (fun i : ℕ => ¬ (p : ℤ) ∣ k₀ + m * i - c p) =
      (range g).filter fun i : ℕ => ∀ q ∈ insert p P, ¬ (q : ℤ) ∣ k₀ + m * i - c q := by
    ext i
    simp only [hS, mem_filter, mem_insert, forall_eq_or_imp]
    tauto
  have e2 : (S.filter (fun i : ℕ => ¬ ¬ (p : ℤ) ∣ k₀ + m * i - c p)).card =
      ((range ((g + p - 1 - i₀) / p)).filter fun j : ℕ =>
        ∀ q ∈ P, ¬ (q : ℤ) ∣ (k₀ + m * i₀) + (m * p : ℕ) * j - c q).card := by
    refine card_nbij' (fun i => i / p) (fun j => i₀ + p * j) ?_ ?_ ?_ ?_
    · intro i hi
      rw [mem_coe, mem_filter, hS, mem_filter, mem_range, not_not] at hi
      obtain ⟨⟨hig, hP⟩, hpc⟩ := hi
      have hdiv := Nat.mod_add_div i p
      rw [hclass i hpc] at hdiv
      rw [mem_coe, mem_filter, mem_range]
      refine ⟨?_, fun q hq => ?_⟩
      · rw [← lt_iff_lt_div hp.pos hi₀, hdiv]; exact hig
      · have := hP q hq
        have hdivZ : (i : ℤ) = i₀ + p * ((i / p : ℕ) : ℤ) := by exact_mod_cast hdiv.symm
        rwa [show (k₀ + m * i₀ : ℤ) + (m * p : ℕ) * (i / p : ℕ) - c q = k₀ + m * i - c q by
          rw [hdivZ, Nat.cast_mul]; ring]
    · intro j hj
      rw [mem_coe, mem_filter, mem_range] at hj
      obtain ⟨hjg, hP⟩ := hj
      rw [mem_coe, mem_filter, hS, mem_filter, mem_range, not_not]
      refine ⟨⟨(lt_iff_lt_div hp.pos hi₀).mpr hjg, fun q hq => ?_⟩, ?_⟩
      · have := hP q hq
        rwa [show (k₀ + m * i₀ : ℤ) + (m * p : ℕ) * j - c q = k₀ + m * (i₀ + p * j : ℕ) - c q by
          push_cast; ring] at this
      · have : k₀ + m * ((i₀ + p * j : ℕ) : ℤ) - c p = (k₀ + m * i₀ - c p) + p * (m * j) := by
          push_cast; ring
        rw [this]; exact dvd_add hc (dvd_mul_right _ _)
    · intro i hi
      rw [mem_coe, mem_filter, hS, mem_filter, not_not] at hi
      have hmod := hclass i hi.2
      have := Nat.mod_add_div i p
      simp only
      omega
    · intro j _
      simp only
      rw [Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hi₀, zero_add]
  unfold surv
  rw [← e1, ← e2, ← hS]
  omega

/-- **Inclusion–exclusion.** With one forbidden class at each of the distinct primes of `P`, and
`p ∤ m` for `p ∈ P`, the survivors number `g ∏_{p ∈ P} (1 - 1/p)` up to `2^{|P|} - 1`. -/
theorem ie_bound (c : ℕ → ℤ) : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ (k₀ : ℤ) (m g : ℕ),
    (∀ p ∈ P, ¬ p ∣ m) →
    |(surv P c k₀ m g : ℚ) - g * ∏ p ∈ P, (1 - 1 / (p : ℚ))| ≤ 2 ^ P.card - 1 := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _ k₀ m g _
    simp [surv]
  | insert p P hpP ih =>
    intro hP k₀ m g hm
    have hp := hP p (mem_insert_self _ _)
    have hmp := hm p (mem_insert_self _ _)
    obtain ⟨i₀, hi₀, hc⟩ := exists_start hp hmp k₀ (c p)
    have hsplit := surv_insert (P := P) hp c k₀ hmp g hi₀ hc
    set g' := (g + p - 1 - i₀) / p with hg'def
    have hPp : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have ih1 := ih hPp k₀ m g (fun q hq => hm q (mem_insert_of_mem hq))
    have ih2 := ih hPp (k₀ + m * i₀) (m * p) g' (fun q hq hdvd => by
      have hqp := hPp q hq
      rcases (Nat.Prime.dvd_mul hqp).mp hdvd with h | h
      · exact hm q (mem_insert_of_mem hq) h
      · exact hpP ((Nat.prime_dvd_prime_iff_eq hqp hp).mp h ▸ hq))
    set Pr := ∏ q ∈ P, (1 - 1 / (q : ℚ)) with hPr
    have hfac : ∀ q ∈ P, 0 ≤ 1 - 1 / (q : ℚ) ∧ 1 - 1 / (q : ℚ) ≤ 1 := fun q hq => by
      have : (1 : ℚ) ≤ q := by exact_mod_cast (hPp q hq).one_lt.le
      constructor
      · rw [sub_nonneg, div_le_one (by linarith)]; exact this
      · have : 0 ≤ 1 / (q : ℚ) := by positivity
        linarith
    have hPr0 : 0 ≤ Pr := prod_nonneg fun q hq => (hfac q hq).1
    have hPr1 : Pr ≤ 1 := prod_le_one₀ (fun q hq => (hfac q hq).1) fun q hq => (hfac q hq).2
    have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
    have hg' : |(g' : ℚ) - g / p| ≤ 1 := by
      have hdm := Nat.div_add_mod (g + p - 1 - i₀) p
      have hml := Nat.mod_lt (g + p - 1 - i₀) hp.pos
      rw [← hg'def] at hdm
      have h1 : p * g' + 1 ≤ g + p := by omega
      have h2 : g < p * g' + p := by omega
      have h1' : (p : ℚ) * g' + 1 ≤ g + p := by exact_mod_cast h1
      have h2' : (g : ℚ) < p * g' + p := by exact_mod_cast h2
      have k1 : (g : ℚ) / p ≤ g' + 1 := by rw [div_le_iff₀ hp0]; nlinarith
      have k2 : ((g' : ℚ) - 1) ≤ g / p := by rw [le_div_iff₀ hp0]; nlinarith
      rw [abs_le]
      constructor <;> linarith
    have hS : (surv (insert p P) c k₀ m g : ℚ) =
        surv P c k₀ m g - surv P c (k₀ + m * i₀) (m * p) g' := by
      rw [hsplit]; push_cast; ring
    rw [prod_insert hpP, card_insert_of_notMem hpP, pow_succ, hS, ← hPr]
    set S1 : ℚ := (surv P c k₀ m g : ℚ)
    set S2 : ℚ := (surv P c (k₀ + m * i₀) (m * p) g' : ℚ)
    have e : S1 - S2 - g * ((1 - 1 / p) * Pr) =
        (S1 - g * Pr) - (S2 - g' * Pr) + (g / p - g') * Pr := by
      field_simp; ring
    rw [e]
    have h3 : |((g : ℚ) / p - g') * Pr| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hPr0, abs_sub_comm]
      calc |(g' : ℚ) - g / p| * Pr ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    have t1 := abs_add_le ((S1 - g * Pr) - (S2 - g' * Pr)) ((g / p - g') * Pr)
    have t2 := abs_sub (S1 - g * Pr) (S2 - g' * Pr)
    have : (2 : ℚ) ^ (#P) * 2 - 1 = (2 ^ #P - 1) + (2 ^ #P - 1) + 1 := by ring
    rw [this]
    linarith

/-! ### The windows `g_t` -/

theorem q_ge (i : ℕ) : i + 5 ≤ q i := by
  induction i with
  | zero => simpa using five_le_q 0
  | succ i ih => have := q_strictMono (show i < i + 1 by omega); omega

/-- **The density of survivors.** For primes from 5, `∏_{p ∈ S} (1 - 1/p) ≥ 4 / (|S| + 4)`,
since the element of rank `i` is at least `q i ≥ i + 5` and `∏_{i < n} (i + 4)/(i + 5)` telescopes. -/
theorem density_ge : ∀ S : Finset ℕ, (∀ p ∈ S, IsQ p) →
    (4 : ℚ) / (S.card + 4) ≤ ∏ p ∈ S, (1 - 1 / (p : ℚ)) := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert m T hT ih =>
    intro hS
    have hmT : m ∉ T := fun h => lt_irrefl _ (hT m h)
    rw [prod_insert hmT, card_insert_of_notMem hmT]
    have hm : (T.card : ℚ) + 5 ≤ m := by
      have := (q_ge T.card).trans (q_le_max hS hT); exact_mod_cast this
    have ih' := ih fun p hp => hS p (mem_insert_of_mem hp)
    have hT0 : (0 : ℚ) < T.card + 4 := by positivity
    have hm0 : (0 : ℚ) < m := by linarith
    have hfac : 1 - 1 / ((T.card : ℚ) + 5) ≤ 1 - 1 / (m : ℚ) := by
      gcongr
    have hfac0 : 0 ≤ 1 - 1 / ((T.card : ℚ) + 5) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    calc (4 : ℚ) / (↑(T.card + 1) + 4) = (1 - 1 / ((T.card : ℚ) + 5)) * (4 / (T.card + 4)) := by
          push_cast; field_simp; ring
      _ ≤ (1 - 1 / (m : ℚ)) * ∏ p ∈ T, (1 - 1 / (p : ℚ)) :=
          mul_le_mul hfac ih' (by positivity) (le_trans hfac0 hfac)

/-- **The window for `t ≥ 27` (`app:prescriptions`).** Among `(t + 4) 2^{t-2}` terms of a
progression of step prime to them, one avoids a prescribed class at each of at most `t` primes
from 5: the survivors number at least `2^t - (2^t - 1)`. -/
theorem tail_survivor {t : ℕ} (ht : 2 ≤ t) (P : Finset ℕ) (hP : ∀ p ∈ P, IsQ p)
    (hcard : P.card ≤ t) (c : ℕ → ℤ) (k₀ : ℤ) (m : ℕ) (hm : ∀ p ∈ P, ¬ p ∣ m) :
    ∃ i < (t + 4) * 2 ^ (t - 2), ∀ p ∈ P, ¬ (p : ℤ) ∣ k₀ + m * i - c p := by
  set g := (t + 4) * 2 ^ (t - 2)
  have hie := ie_bound c P (fun p hp => (hP p hp).1) k₀ m g hm
  have hd := density_ge P hP
  have hpos : (1 : ℚ) ≤ surv P c k₀ m g := by
    have h1 := (abs_le.mp hie).1
    have h2 : (4 : ℚ) / (t + 4) ≤ 4 / (P.card + 4) := by
      gcongr
    have h3 : (2 : ℚ) ^ P.card ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) hcard
    have hg : (g : ℚ) * (4 / (t + 4)) = 2 ^ t := by
      have : (2 : ℚ) ^ t = 2 ^ (t - 2) * 4 := by
        rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel ht]
      rw [this]; push_cast [g]; field_simp
    have hg0 : (0 : ℚ) ≤ g := by positivity
    have : (2 : ℚ) ^ t ≤ g * ∏ p ∈ P, (1 - 1 / (p : ℚ)) := by
      rw [← hg]; exact mul_le_mul_of_nonneg_left (h2.trans hd) hg0
    linarith
  have hpos' : 0 < surv P c k₀ m g := by exact_mod_cast lt_of_lt_of_le zero_lt_one hpos
  obtain ⟨i, hi⟩ := card_pos.mp hpos'
  rw [mem_filter, mem_range] at hi
  exact ⟨i, hi.1, hi.2⟩

/-- `⌈g / p⌉` is antitone in `p`. -/
theorem ceil_div_antitone (g : ℕ) : AntitoneOn (fun p => (g + p - 1) / p) (Set.Ici 1) := by
  intro p hp p' hp' hle
  simp only [Set.mem_Ici] at hp hp'
  simp only
  set x := (g + p' - 1) / p'
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hx : x * p' ≤ g + p' - 1 := Nat.div_mul_le_self _ _
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · rw [h0]; omega
  · have : x * p ≤ x * p' - x * (p' - p) := by
      rw [← Nat.mul_sub]; exact Nat.mul_le_mul_left _ (by omega)
    have : x * (p' - p) ≥ p' - p := Nat.le_mul_of_pos_left _ h0
    omega

theorem gList_spec : ∀ t (ht : t < gList.length),
    ∑ i ∈ range t, (gList[t] + qList[i]! - 1) / qList[i]! < gList[t] := by
  decide +kernel

theorem q_eq_list' {i : ℕ} (hi : i < 28) : q i = qList[i]! := by
  rw [q_eq_list (by simpa [qList] using hi), getElem!_pos qList i (by simpa [qList] using hi)]

/-- A forbidden set meeting at most one class modulo `p` lies in the class of some `c`. -/
theorem exists_class {p : ℕ} {bad : ℤ → Prop} (h1 : AtMostClasses p 1 bad) :
    ∃ c : ℤ, ∀ k, bad k → (p : ℤ) ∣ k - c := by
  by_cases h : ∃ k₀, bad k₀
  · obtain ⟨k₀, hk₀⟩ := h
    refine ⟨k₀, fun k hk => ?_⟩
    by_contra hnd
    obtain ⟨k', hk', hnb⟩ := h1 [k, k₀] rfl (by simpa using hnd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    rcases hk' with rfl | rfl
    · exact hnb hk
    · exact hnb hk₀
  · push Not at h
    exact ⟨0, fun k hk => absurd hk (h k)⟩

/-- **The window `g_t` (`sec:high`).** Among `g_t` terms of a progression of step prime to them,
one avoids a prescribed class at each of at most `t` primes from 5. -/
theorem window_survivor (t : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, IsQ p) (hcard : P.card ≤ t)
    (c : ℕ → ℤ) (k₀ : ℤ) (m : ℕ) (hm : ∀ p ∈ P, ¬ p ∣ m) :
    ∃ i < gWin t, ∀ p ∈ P, ¬ (p : ℤ) ∣ k₀ + m * i - c p := by
  unfold gWin
  split_ifs with ht
  · classical
    set g := gList[t]'(by simp [gList]; omega)
    refine ap_sieve k₀ m g P (fun _ => 1) (fun p k => (p : ℤ) ∣ k - c p) (fun p hp => ?_) ?_
    · refine ⟨(hP p hp).1, hm p hp, fun k k' hkk => ?_, fun ks hlen hpair => ?_⟩
      · constructor <;> intro h
        · have := dvd_sub h hkk; rwa [show k - c p - (k - k') = k' - c p by ring] at this
        · have := dvd_add h hkk; rwa [show k' - c p + (k - k') = k - c p by ring] at this
      · match ks, hlen, hpair with
        | [u, v], _, hpair =>
          simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at hpair
          by_contra hall
          simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
            exists_eq_left, not_or, not_not] at hall
          exact hpair (by have := dvd_sub hall.1 hall.2; rwa [show u - c p - (v - c p) = u - v by
            ring] at this)
    · have hle : ∑ p ∈ P, 1 * ((g + p - 1) / p) ≤ ∑ i ∈ range P.card, (g + q i - 1) / q i := by
        simp only [one_mul]
        exact sum_le_sum_q (fun p => (g + p - 1) / p)
          (fun a b ha hab => ceil_div_antitone g (show 1 ≤ a by omega) (show 1 ≤ b by omega) hab)
          P hP
      have hle2 : ∑ i ∈ range P.card, (g + q i - 1) / q i ≤ ∑ i ∈ range t, (g + q i - 1) / q i :=
        sum_le_sum_of_subset (range_subset_range.mpr hcard)
      have heq : ∑ i ∈ range t, (g + q i - 1) / q i =
          ∑ i ∈ range t, (g + qList[i]! - 1) / qList[i]! :=
        sum_congr rfl fun i hi => by rw [q_eq_list' (by simp at hi; omega)]
      have := gList_spec t (by simp [gList]; omega)
      change ∑ i ∈ range t, (g + qList[i]! - 1) / qList[i]! < g at this
      omega
  · exact tail_survivor (by omega) P hP hcard c k₀ m hm

/-- The window `g_t` with forbidden sets meeting at most one class modulo each prime. -/
theorem window_survivor' (t : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, IsQ p) (hcard : P.card ≤ t)
    (bad : ℕ → ℤ → Prop) (hbad : ∀ p ∈ P, AtMostClasses p 1 (bad p)) (k₀ : ℤ) (m : ℕ)
    (hm : ∀ p ∈ P, ¬ p ∣ m) : ∃ i < gWin t, ∀ p ∈ P, ¬ bad p (k₀ + m * i) := by
  classical
  have hc : ∀ p, ∃ c : ℤ, p ∈ P → ∀ k, bad p k → (p : ℤ) ∣ k - c := fun p => by
    by_cases hp : p ∈ P
    · obtain ⟨c, hc⟩ := exists_class (hbad p hp); exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose c hc using hc
  obtain ⟨i, hi, hgood⟩ := window_survivor t P hP hcard c k₀ m hm
  exact ⟨i, hi, fun p hp hb => hgood p hp (hc p hp _ hb)⟩

/-! ### The comparison for `t ≥ 27` -/

theorem gWin_tail {t : ℕ} (ht : 27 ≤ t) : gWin t = (t + 4) * 2 ^ (t - 2) := by
  unfold gWin; split_ifs with h; · omega
  rfl

theorem P_succ (t : ℕ) : P (t + 1) = P t * q t := prod_range_succ _ _

theorem q_ge_113 {t : ℕ} (ht : 27 ≤ t) : 113 ≤ q t := by
  have h27 : q 27 = 113 := by rw [q_eq_list' (by norm_num)]; rfl
  rw [← h27]; exact q_mono ht

theorem P_27 : P 27 = ∏ i ∈ range 27, qList[i]! :=
  prod_congr rfl fun i hi => q_eq_list' (by simp at hi; omega)

/-- `16 (t + 5)⁴ ≤ 19 (t + 4)⁴` for `t ≥ 27`, from `(t + 5)/(t + 4) ≤ 32/31`. -/
theorem tail_growth {t : ℕ} (ht : 27 ≤ t) : 16 * (t + 5) ^ 4 ≤ 19 * (t + 4) ^ 4 := by
  have h1 : 31 * (t + 5) ≤ 32 * (t + 4) := by omega
  have h2 : (31 * (t + 5)) ^ 4 ≤ (32 * (t + 4)) ^ 4 := Nat.pow_le_pow_left h1 4
  rw [mul_pow, mul_pow] at h2
  have h3 : 31 ^ 4 * (16 * (t + 5) ^ 4) ≤ 31 ^ 4 * (19 * (t + 4) ^ 4) := by
    calc 31 ^ 4 * (16 * (t + 5) ^ 4) = 16 * (31 ^ 4 * (t + 5) ^ 4) := by ring
      _ ≤ 16 * (32 ^ 4 * (t + 4) ^ 4) := Nat.mul_le_mul_left _ h2
      _ ≤ 31 ^ 4 * (19 * (t + 4) ^ 4) := by
        rw [show 16 * (32 ^ 4 * (t + 4) ^ 4) = 16777216 * (t + 4) ^ 4 by ring,
          show 31 ^ 4 * (19 * (t + 4) ^ 4) = 17546899 * (t + 4) ^ 4 by ring]
        exact Nat.mul_le_mul_right _ (by norm_num)
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

/-- **The comparison of `app:prescriptions` for `t ≥ 27`:** `√(3 P_t / 4) > 3066 g_t²`, in the
form `4 (3066 g_t²)² < 3 P_t`. It holds at `t = 27`, and persists since `P_t` grows by
`q_t ≥ 113` while `g_t⁴` grows by `16 ((t + 5)/(t + 4))⁴ ≤ 19`. -/
theorem tail_ineq {t : ℕ} (ht : 27 ≤ t) : 4 * (3066 * gWin t ^ 2) ^ 2 < 3 * P t := by
  induction t, ht using Nat.le_induction with
  | base =>
    rw [gWin_tail le_rfl, P_27]
    decide +kernel
  | succ t ht ih =>
    rw [gWin_tail (by omega)] at ih ⊢
    rw [P_succ]
    have hq := q_ge_113 ht
    have hg := tail_growth ht
    -- `g_{t+1}⁴ = 16 (t + 5)⁴ 2^{4(t-2)}` and `g_t⁴ = (t + 4)⁴ 2^{4(t-2)}`
    have e : (t + 1 + 4) * 2 ^ (t + 1 - 2) = 2 * ((t + 5) * 2 ^ (t - 2)) := by
      rw [show t + 1 - 2 = (t - 2) + 1 by omega, pow_succ]; ring
    rw [e]
    set A := 2 ^ (t - 2)
    have key : 4 * (3066 * (2 * ((t + 5) * A)) ^ 2) ^ 2 ≤ 19 * (4 * (3066 * ((t + 4) * A) ^ 2) ^ 2) := by
      have : 4 * (3066 * (2 * ((t + 5) * A)) ^ 2) ^ 2 = (16 * (t + 5) ^ 4) * (4 * 3066 ^ 2 * A ^ 4) := by
        ring
      rw [this, show 19 * (4 * (3066 * ((t + 4) * A) ^ 2) ^ 2) =
        (19 * (t + 4) ^ 4) * (4 * 3066 ^ 2 * A ^ 4) by ring]
      exact Nat.mul_le_mul_right _ hg
    calc 4 * (3066 * (2 * ((t + 5) * A)) ^ 2) ^ 2 ≤ 19 * (4 * (3066 * ((t + 4) * A) ^ 2) ^ 2) := key
      _ < 19 * (3 * P t) := by omega
      _ ≤ 3 * (P t * q t) := by nlinarith

end KimKimOh.Windows

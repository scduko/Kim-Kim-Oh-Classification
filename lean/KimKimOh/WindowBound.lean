import KimKimOh.FirstPass
import Mathlib.Data.List.Prime
import KimKimOh.Compute.WindowBound

/-!
# A computable bound for the sieve sum of the first pass

For `Δ > 0`, the primes `p ≥ 5` dividing `Δ` split into the small ones (`p ≤ 47`), found from
`gs = gcd(Δ, 5·7·…·47)`, and the large ones (`p ≥ 53`), counted by size: their product divides
`Δ / gs`, so there are at most `largeBound (Δ / gs)`. A large prime of weight 2 divides
`gcd(Δ, δ)`, so there are at most `largeBound (gcd(Δ, δ))` of them. `ubound` adds the exact
contributions of the small primes and `⌈g / 53⌉` for each large prime and weight
(`sum_le_ubound`).
-/

namespace KimKimOh

open Finset

/-! ### Soundness -/

theorem recsum_eq (f : ℕ → ℕ) : ∀ l : List ℕ,
    List.rec (motive := fun _ => ℕ) 0 (fun p _ r => f p + r) l = (l.map f).sum
  | [] => rfl
  | x :: l => by
    show f x + List.rec (motive := fun _ => ℕ) 0 (fun p _ r => f p + r) l = _
    rw [recsum_eq f l, List.map_cons, List.sum_cons]

theorem smallPrimes_spec : ∀ p ∈ smallPrimes, p.Prime ∧ 5 ≤ p := by
  intro p hp
  simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

theorem mem_smallPrimes {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h47 : p ≤ 47) : p ∈ smallPrimes := by
  interval_cases p <;> first | (simp [smallPrimes]; done) | (exfalso; norm_num at hp)

theorem dvd_prim47 {p : ℕ} (hp : p ∈ smallPrimes) : p ∣ prim47 := by
  simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem blt_false {n k : ℕ} (h : ¬ n < k) : Nat.blt n k = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.blt_eq.mp h')

theorem small_gcd_check : ∀ g < 35, ∀ p ∈ smallPrimes,
    (prim47 % g == 0 && g % p == 0) = true → p = g := by
  decide

/-- Every small prime dividing `Δ` lies in `smallOf (gcd Δ prim47)`. -/
theorem mem_smallOf {Δ p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h47 : p ≤ 47) (hd : p ∣ Δ) :
    p ∈ smallOf (Nat.gcd Δ prim47) := by
  have hps := mem_smallPrimes hp h5 h47
  have hg : p ∣ Nat.gcd Δ prim47 := Nat.dvd_gcd hd (dvd_prim47 hps)
  unfold smallOf
  by_cases h1 : Nat.gcd Δ prim47 = 1
  · exact absurd (Nat.le_of_dvd one_pos (h1 ▸ hg)) (by omega)
  · have h1' : (Nat.gcd Δ prim47 == 1) = false := by simpa using h1
    rw [h1', Bool.cond_false]
    by_cases h35 : Nat.gcd Δ prim47 < 35
    · rw [show Nat.blt (Nat.gcd Δ prim47) 35 = true from Nat.blt_eq.mpr h35, Bool.cond_true,
        List.mem_singleton]
      refine small_gcd_check _ h35 p hps ?_
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right _ _), Nat.mod_eq_zero_of_dvd hg⟩
    · rw [blt_false h35, Bool.cond_false]
      have key : ∀ l : List ℕ, p ∈ l → p ∈ List.rec (motive := fun _ => List ℕ) []
          (fun q _ r => cond (Nat.gcd Δ prim47 % q == 0) (q :: r) r) l := by
        intro l hl
        induction l with
        | nil => simp at hl
        | cons q l ih =>
          simp only
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [show (Nat.gcd Δ prim47 % p == 0) = true by simpa using Nat.mod_eq_zero_of_dvd hg]
            exact List.mem_cons_self
          · cases (Nat.gcd Δ prim47 % q == 0)
            · exact ih hl
            · exact List.mem_cons_of_mem _ (ih hl)
      exact key _ hps

/-- `r` distinct primes `≥ 53` with product at most `n` number at most `largeBound n`. -/
theorem card_le_largeBound {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ 53 ≤ p) {n : ℕ}
    (hprod : ∏ p ∈ S, p ≤ n) : S.card ≤ largeBound n := by
  have h53 : 53 ^ S.card ≤ n := by
    calc 53 ^ S.card = ∏ _p ∈ S, 53 := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod fun p hp => (hS p hp).2
      _ ≤ n := hprod
  unfold largeBound
  by_cases h1 : n < 53
  · have : S.card = 0 := by
      by_contra h0
      have : 53 ≤ 53 ^ S.card := Nat.le_self_pow h0 53
      omega
    simp [this]
  rw [blt_false h1]
  by_cases h2 : n < 2809
  · rw [show Nat.blt n 2809 = true from Nat.blt_eq.mpr h2]
    by_contra hc; push Not at hc
    have : 53 ^ 2 ≤ 53 ^ S.card := Nat.pow_le_pow_right (by norm_num) (by simp at hc; omega)
    simp at this ⊢; omega
  rw [blt_false h2]
  by_cases h3 : n < 148877
  · rw [show Nat.blt n 148877 = true from Nat.blt_eq.mpr h3]
    by_contra hc; push Not at hc
    have : 53 ^ 3 ≤ 53 ^ S.card := Nat.pow_le_pow_right (by norm_num) (by simp at hc; omega)
    simp at this ⊢; omega
  rw [blt_false h3]
  by_cases h4 : n < 7890481
  · rw [show Nat.blt n 7890481 = true from Nat.blt_eq.mpr h4]
    by_contra hc; push Not at hc
    have : 53 ^ 4 ≤ 53 ^ S.card := Nat.pow_le_pow_right (by norm_num) (by simp at hc; omega)
    simp at this ⊢; omega
  rw [blt_false h4]
  simp only [Bool.cond_false]
  exact (Nat.lt_pow_self (by norm_num : 1 < 53)).le.trans h53

theorem prim47_eq : prim47 = smallPrimes.prod := by decide

theorem le_47_of_dvd_prim47 {p : ℕ} (hp : p.Prime) (hd : p ∣ prim47) : p ≤ 47 := by
  rw [prim47_eq] at hd
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_prod_iff hp.prime).mp hd
  have hqp := (smallPrimes_spec q hq).1
  rw [(Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq]
  simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hq
  omega

theorem toFinset_sum_le (f : ℕ → ℕ) : ∀ l : List ℕ, ∑ x ∈ l.toFinset, f x ≤ (l.map f).sum
  | [] => by simp
  | x :: l => by
    rw [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases hx : x ∈ l.toFinset
    · rw [Finset.insert_eq_of_mem hx]; exact (toFinset_sum_le f l).trans (Nat.le_add_left _ _)
    · rw [Finset.sum_insert hx]; exact Nat.add_le_add_left (toFinset_sum_le f l) _

theorem wtN_le_succ (δ cnt p : ℕ) : wtN δ cnt p ≤ 1 + if δ % p = 0 then 1 else 0 := by
  unfold wtN
  by_cases h : δ % p = 0
  · simp only [h, ite_true]; cases (!(cnt % p == 0)) <;> simp
  · simp [h]

/-- **The sieve sum is at most `ubound`.** -/
theorem sum_le_ubound (Δ δ cnt g : ℕ) (hΔ : 0 < Δ) :
    ∑ p ∈ Δ.primeFactors.filter (5 ≤ ·), wtN δ cnt p * ((g + p - 1) / p) ≤ ubound Δ δ cnt g := by
  classical
  set P := Δ.primeFactors.filter (5 ≤ ·) with hP
  set gs := Nat.gcd Δ prim47 with hgs
  have hmemP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p ∧ p ∣ Δ := by
    intro p hp
    rw [hP, Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ⟨hp.1.1, hp.2, hp.1.2.1⟩
  rw [← Finset.sum_filter_add_sum_filter_not P (· ≤ 47)]
  unfold ubound
  rw [recsum_eq]
  apply Nat.add_le_add
  · -- the small primes
    refine (Finset.sum_le_sum_of_subset (fun p hp => ?_)).trans
      (toFinset_sum_le (fun p => wtN δ cnt p * ((g + p - 1) / p)) _)
    rw [Finset.mem_filter] at hp
    obtain ⟨hpp, h5, hd⟩ := hmemP p hp.1
    exact List.mem_toFinset.mpr (mem_smallOf hpp h5 hp.2 hd)
  · -- the large primes
    set Pl := P.filter (fun p => ¬ p ≤ 47) with hPl
    have hlarge : ∀ p ∈ Pl, p.Prime ∧ 53 ≤ p ∧ p ∣ Δ := by
      intro p hp
      rw [hPl, Finset.mem_filter] at hp
      obtain ⟨hpp, h5, hd⟩ := hmemP p hp.1
      refine ⟨hpp, ?_, hd⟩
      by_contra hlt
      push Not at hlt
      interval_cases p <;> norm_num at hpp <;> omega
    have hceil : ∀ p ∈ Pl, (g + p - 1) / p ≤ (g + 52) / 53 := by
      intro p hp
      have h53 := (hlarge p hp).2.1
      have := Windows.ceil_div_antitone g (show (53 : ℕ) ∈ Set.Ici 1 by simp)
        (show p ∈ Set.Ici 1 by simp; omega) h53
      simpa using this
    calc ∑ p ∈ Pl, wtN δ cnt p * ((g + p - 1) / p)
        ≤ ∑ p ∈ Pl, wtN δ cnt p * ((g + 52) / 53) :=
          Finset.sum_le_sum fun p hp => Nat.mul_le_mul_left _ (hceil p hp)
      _ = (∑ p ∈ Pl, wtN δ cnt p) * ((g + 52) / 53) := by rw [Finset.sum_mul]
      _ ≤ (largeBound (Δ / gs) + largeBound (Nat.gcd Δ δ)) * ((g + 52) / 53) := by
          apply Nat.mul_le_mul_right
          -- `Σ wt = |Pl| + |{wt = 2}|`
          have hsplit : ∑ p ∈ Pl, wtN δ cnt p ≤ Pl.card + (Pl.filter (fun p => δ % p = 0)).card := by
            calc ∑ p ∈ Pl, wtN δ cnt p ≤ ∑ p ∈ Pl, (1 + if δ % p = 0 then 1 else 0) :=
                  Finset.sum_le_sum fun p _ => wtN_le_succ δ cnt p
              _ = Pl.card + (Pl.filter (fun p => δ % p = 0)).card := by
                  rw [Finset.sum_add_distrib, Finset.sum_boole]; simp
          refine hsplit.trans (Nat.add_le_add ?_ ?_)
          · -- the product of the large primes divides `Δ / gs`
            refine card_le_largeBound (fun p hp => ⟨(hlarge p hp).1, (hlarge p hp).2.1⟩) ?_
            have hdvd : ∏ p ∈ Pl, p ∣ Δ :=
              Finset.prod_primes_dvd Δ (fun p hp => (hlarge p hp).1.prime)
                (fun p hp => (hlarge p hp).2.2)
            have hcop : Nat.Coprime (∏ p ∈ Pl, p) gs := by
              refine Nat.Coprime.prod_left fun p hp => ?_
              refine ((hlarge p hp).1.coprime_iff_not_dvd).mpr fun hd => ?_
              have := le_47_of_dvd_prim47 (hlarge p hp).1 (hd.trans (Nat.gcd_dvd_right _ _))
              have := (hlarge p hp).2.1
              omega
            have hgsd : gs ∣ Δ := Nat.gcd_dvd_left _ _
            have hgs0 : 0 < gs := Nat.gcd_pos_of_pos_left _ hΔ
            have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd hgsd
            exact (Nat.le_div_iff_mul_le hgs0).mpr (Nat.le_of_dvd hΔ this)
          · refine card_le_largeBound (fun p hp => by
              rw [Finset.mem_filter] at hp
              exact ⟨(hlarge p hp.1).1, (hlarge p hp.1).2.1⟩) ?_
            have hdvd : ∏ p ∈ Pl.filter (fun p => δ % p = 0), p ∣ Nat.gcd Δ δ := by
              refine Finset.prod_primes_dvd _ (fun p hp => ?_) (fun p hp => ?_)
              · rw [Finset.mem_filter] at hp; exact (hlarge p hp.1).1.prime
              · rw [Finset.mem_filter] at hp
                exact Nat.dvd_gcd (hlarge p hp.1).2.2 (Nat.dvd_of_mod_eq_zero hp.2)
            exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hΔ) hdvd

end KimKimOh

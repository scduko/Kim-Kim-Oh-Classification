import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# A sieve for Kim–Kim–Oh, §4

Kim–Kim–Oh choose an integer `s` such that `sa + b` avoids the primes `p ≥ 5` dividing `a - 18`,
with `|s|` small compared with `a` (their Lemma 3 and Steps 1–5). We prove (`exists_shift`): for
`a > 72` even and any `b` there is `s` with `24 (s² + |s| + 1) < a` and `p ∤ b + 18 s` for every
prime `p ≥ 5` dividing `a - 18`. (Modulo such a `p`, `b + 18 s ≡ b + a s`.)

* `legendre`: the Legendre sieve with explicit error. Let `P` be a set of primes, none dividing
  `m` or `Q`. Among the `j < n` with `j ≡ c (mod Q)`, the number of `j` with `x₀ + m j` prime to
  every `p ∈ P` is `(n/Q) ∏ (1 - 1/p)` up to `2^|P|`. Induction on `P`: the `j` with
  `p ∣ x₀ + m j` form a residue class modulo `p`, so by the Chinese remainder theorem the
  excluded `j` form a residue class modulo `Q p`; `Nat.count_modEq_card` counts residue classes.
* For `|P| ≤ 3` a union bound on 3 or 7 consecutive values of `s`; for `|P| = t ≥ 4` the
  Legendre sieve on `2S + 1` values with `S = (t + 4) 2^(t-3)`, using `∏ (1 - 1/p) ≥ 4/(t + 4)`
  and `a - 18 ≥ 2 ∏ p ≥ 2 · 5 · 7 ⋯ (2t + 3)` (the primes are distinct, odd and at least 5).
-/

namespace KimKimOh.Sieve

open Finset

/-! ### Counting residue classes -/

/-- The number of `j < n` with `j ≡ c (mod Q)` is `n/Q` up to `1`. -/
theorem card_modEq (n Q c : ℕ) (hQ : 0 < Q) :
    |((#{j ∈ range n | j ≡ c [MOD Q]} : ℕ) : ℝ) - n / Q| ≤ 1 := by
  have h := Nat.count_modEq_card (b := n) hQ c
  rw [Nat.count_eq_card_filter_range] at h
  rw [h]
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h1 : ((n / Q : ℕ) : ℝ) ≤ (n : ℝ) / Q := Nat.cast_div_le
  have h2 : (n : ℝ) / Q < ((n / Q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hQ']
    have := Nat.lt_div_mul_add (a := n) hQ
    have : (n : ℝ) < ((n / Q * Q + Q : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  rw [abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-! ### The Legendre sieve -/

/-- The `j < n` with `j ≡ c (mod Q)` and `x₀ + m j` prime to every `p ∈ P`. -/
def good (P : Finset ℕ) (x0 m : ℤ) (n Q c : ℕ) : ℕ :=
  #{j ∈ range n | j ≡ c [MOD Q] ∧ ∀ p ∈ P, ¬ (p : ℤ) ∣ x0 + m * j}

/-- `q ∣ x₀ + m j` is a congruence condition on `j` when `q ∤ m`. -/
theorem exists_root (q : ℕ) (hq : q.Prime) (x0 m : ℤ) (hm : ¬ (q : ℤ) ∣ m) :
    ∃ j0 : ℕ, ∀ j : ℕ, (q : ℤ) ∣ x0 + m * j ↔ j ≡ j0 [MOD q] := by
  have := Fact.mk hq
  have hm' : (m : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((-(x0 : ZMod q)) / m).val, fun j => ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  push_cast
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- **The Legendre sieve.** -/
theorem legendre (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x0 m : ℤ) (hm : ∀ p ∈ P, ¬ (p : ℤ) ∣ m) (n : ℕ) :
    ∀ Q c : ℕ, 0 < Q → (∀ p ∈ P, ¬ p ∣ Q) →
      |((good P x0 m n Q c : ℕ) : ℝ) - n / Q * ∏ p ∈ P, (1 - 1 / (p : ℝ))| ≤ 2 ^ P.card := by
  induction P using Finset.induction_on with
  | empty =>
    intro Q c hQ _
    have h := card_modEq n Q c hQ
    simpa [good] using h
  | @insert q P hqP ih =>
    intro Q c hQ hPQ
    have hq : q.Prime := hP q (mem_insert_self _ _)
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have hm' : ∀ p ∈ P, ¬ (p : ℤ) ∣ m := fun p hp => hm p (mem_insert_of_mem hp)
    have hqm : ¬ (q : ℤ) ∣ m := hm q (mem_insert_self _ _)
    have hqQ : ¬ q ∣ Q := hPQ q (mem_insert_self _ _)
    obtain ⟨j0, hj0⟩ := exists_root q hq x0 m hqm
    have hcop : Nat.Coprime Q q := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqQ))
    -- the Chinese remainder theorem
    obtain ⟨c', hc'⟩ : ∃ c' : ℕ, ∀ j, (j ≡ c [MOD Q] ∧ j ≡ j0 [MOD q]) ↔ j ≡ c' [MOD Q * q] := by
      refine ⟨Nat.chineseRemainder hcop c j0, fun j => ?_⟩
      have h1 := (Nat.chineseRemainder hcop c j0).2.1
      have h2 := (Nat.chineseRemainder hcop c j0).2.2
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
      constructor
      · rintro ⟨ha, hb⟩; exact ⟨ha.trans h1.symm, hb.trans h2.symm⟩
      · rintro ⟨ha, hb⟩; exact ⟨ha.trans h1, hb.trans h2⟩
    have hsplit : (good (insert q P) x0 m n Q c : ℤ) = good P x0 m n Q c - good P x0 m n (Q * q) c' := by
      have hsub : (range n).filter (fun j => j ≡ c' [MOD Q * q] ∧ ∀ p ∈ P, ¬ (p : ℤ) ∣ x0 + m * j) ⊆
          (range n).filter (fun j => j ≡ c [MOD Q] ∧ ∀ p ∈ P, ¬ (p : ℤ) ∣ x0 + m * j) := by
        intro j hj
        simp only [mem_filter] at hj ⊢
        exact ⟨hj.1, ((hc' j).mpr hj.2.1).1, hj.2.2⟩
      have hdiff : (range n).filter (fun j => j ≡ c [MOD Q] ∧ ∀ p ∈ insert q P, ¬ (p : ℤ) ∣ x0 + m * j) =
          (range n).filter (fun j => j ≡ c [MOD Q] ∧ ∀ p ∈ P, ¬ (p : ℤ) ∣ x0 + m * j) \
          (range n).filter (fun j => j ≡ c' [MOD Q * q] ∧ ∀ p ∈ P, ¬ (p : ℤ) ∣ x0 + m * j) := by
        ext j
        simp only [mem_filter, mem_sdiff, mem_insert, forall_eq_or_imp]
        constructor
        · rintro ⟨hj, hc, hqj, hPj⟩
          refine ⟨⟨hj, hc, hPj⟩, fun ⟨_, hc'j, _⟩ => hqj ((hj0 j).mpr ((hc' j).mpr hc'j).2)⟩
        · rintro ⟨⟨hj, hc, hPj⟩, hn⟩
          refine ⟨hj, hc, fun hqj => hn ⟨hj, (hc' j).mp ⟨hc, (hj0 j).mp hqj⟩, hPj⟩, hPj⟩
      unfold good
      rw [hdiff, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
    have hQq : 0 < Q * q := Nat.mul_pos hQ hq.pos
    have hPQq : ∀ p ∈ P, ¬ p ∣ Q * q := by
      intro p hp hdvd
      rcases (Nat.Prime.dvd_mul (hP' p hp)).mp hdvd with h | h
      · exact hPQ p (mem_insert_of_mem hp) h
      · have := (Nat.prime_dvd_prime_iff_eq (hP' p hp) hq).mp h
        exact hqP (this ▸ hp)
    have h1 := ih hP' hm' Q c hQ (fun p hp => hPQ p (mem_insert_of_mem hp))
    have h2 := ih hP' hm' (Q * q) c' hQq hPQq
    set Pr := ∏ p ∈ P, (1 - 1 / (p : ℝ))
    have hsplitR : ((good (insert q P) x0 m n Q c : ℕ) : ℝ) =
        (good P x0 m n Q c : ℝ) - (good P x0 m n (Q * q) c' : ℝ) := by
      exact_mod_cast hsplit
    rw [prod_insert hqP, card_insert_of_notMem hqP, hsplitR, pow_succ]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    have e : (n : ℝ) / Q * ((1 - 1 / (q : ℝ)) * Pr) = n / Q * Pr - n / ((Q * q : ℕ) : ℝ) * Pr := by
      push_cast; field_simp
    rw [e]
    calc |(good P x0 m n Q c : ℝ) - good P x0 m n (Q * q) c' - (n / Q * Pr - n / ((Q * q : ℕ) : ℝ) * Pr)|
        = |((good P x0 m n Q c : ℝ) - n / Q * Pr) - ((good P x0 m n (Q * q) c' : ℝ) - n / ((Q * q : ℕ) : ℝ) * Pr)| := by
          ring_nf
      _ ≤ |(good P x0 m n Q c : ℝ) - n / Q * Pr| + |(good P x0 m n (Q * q) c' : ℝ) - n / ((Q * q : ℕ) : ℝ) * Pr| :=
          abs_sub _ _
      _ ≤ 2 ^ P.card + 2 ^ P.card := add_le_add h1 h2
      _ = 2 ^ P.card * 2 := by ring

/-- **A value avoiding all residue classes.** If `n ∏ (1 - 1/p) > 2^|P|`, some `j < n` has
`x₀ + m j` prime to every `p ∈ P`. -/
theorem exists_good (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x0 m : ℤ) (hm : ∀ p ∈ P, ¬ (p : ℤ) ∣ m) (n : ℕ)
    (hn : (2 : ℝ) ^ P.card < n * ∏ p ∈ P, (1 - 1 / (p : ℝ))) :
    ∃ j < n, ∀ p ∈ P, ¬ (p : ℤ) ∣ x0 + m * j := by
  have h := legendre P hP x0 m hm n 1 0 one_pos (fun p hp h => (hP p hp).one_lt.ne' (Nat.dvd_one.mp h))
  rw [Nat.cast_one, div_one] at h
  have hpos : 0 < good P x0 m n 1 0 := by
    have := (abs_le.mp h).1
    have : (0 : ℝ) < good P x0 m n 1 0 := by linarith
    exact_mod_cast this
  obtain ⟨j, hj⟩ := card_pos.mp hpos
  simp only [mem_filter, mem_range] at hj
  exact ⟨j, hj.1, hj.2.2⟩

/-! ### The union bound -/

/-- At most `n/p + 1` of the `j < n` have `p ∣ x₀ + m j`, and at most `n / p` when `p ∣ n`. -/
theorem card_bad_le (p : ℕ) (hp : p.Prime) (x0 m : ℤ) (hm : ¬ (p : ℤ) ∣ m) (n : ℕ) :
    #((range n).filter fun j : ℕ => (p : ℤ) ∣ x0 + m * (j : ℤ)) ≤ n / p + if n % p = 0 then 0 else 1 := by
  obtain ⟨j0, hj0⟩ := exists_root p hp x0 m hm
  have e : (range n).filter (fun j : ℕ => (p : ℤ) ∣ x0 + m * (j : ℤ)) = (range n).filter (fun j => j ≡ j0 [MOD p]) :=
    filter_congr fun j _ => hj0 j
  rw [e, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card (b := n) hp.pos j0]
  split_ifs with h1 h2 h2 <;> omega

/-- **The union bound.** -/
theorem exists_good_union (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x0 m : ℤ) (hm : ∀ p ∈ P, ¬ (p : ℤ) ∣ m)
    (n : ℕ) (hn : ∑ p ∈ P, (n / p + if n % p = 0 then 0 else 1) < n) :
    ∃ j < n, ∀ p ∈ P, ¬ (p : ℤ) ∣ x0 + m * j := by
  by_contra hcon
  push Not at hcon
  have hsub : range n ⊆ P.biUnion fun p => (range n).filter fun j : ℕ => (p : ℤ) ∣ x0 + m * (j : ℤ) := by
    intro j hj
    obtain ⟨p, hp, hpj⟩ := hcon j (mem_range.mp hj)
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hj, hpj⟩⟩
  have h1 := card_le_card hsub
  have h2 := card_biUnion_le (s := P) (t := fun p => (range n).filter fun j : ℕ => (p : ℤ) ∣ x0 + m * (j : ℤ))
  have h3 : ∑ p ∈ P, #((range n).filter fun j : ℕ => (p : ℤ) ∣ x0 + m * (j : ℤ)) ≤
      ∑ p ∈ P, (n / p + if n % p = 0 then 0 else 1) :=
    sum_le_sum fun p hp => card_bad_le p (hP p hp) x0 m (hm p hp) n
  rw [card_range] at h1
  omega

/-! ### Products over primes at least 5 -/

/-- `∏ (1 - 1/p) ≥ 4/(t + 4)` for `t` distinct integers `p ≥ 5`. -/
theorem prod_one_sub_inv_ge (P : Finset ℕ) (hP : ∀ p ∈ P, 5 ≤ p) :
    (4 : ℝ) / (P.card + 4) ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert q P hlt ih =>
    have hqP : q ∉ P := fun h => lt_irrefl q (hlt q h)
    have hq5 := hP q (mem_insert_self _ _)
    have ih' := ih fun p hp => hP p (mem_insert_of_mem hp)
    rw [prod_insert hqP, card_insert_of_notMem hqP]
    -- `q ≥ |P| + 5`: the elements of `P` lie in `[5, q)`
    have hcard : P.card ≤ q - 5 := by
      have : P ⊆ Ico 5 q := fun p hp => mem_Ico.mpr ⟨hP p (mem_insert_of_mem hp), hlt p hp⟩
      simpa using card_le_card this
    have hqge : (P.card : ℝ) + 5 ≤ q := by
      have : P.card + 5 ≤ q := by omega
      exact_mod_cast this
    have hq0 : (0 : ℝ) < q := by positivity
    have hf : (P.card + 4 : ℝ) / (P.card + 5) ≤ 1 - 1 / (q : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 / (q : ℝ) ≤ 1 / (P.card + 5) := one_div_le_one_div_of_le (by positivity) hqge
      have e : (1 - 1 / (q : ℝ)) * (P.card + 5) = P.card + 5 - (P.card + 5) / q := by
        field_simp
      rw [e]
      have : ((P.card : ℝ) + 5) / q ≤ 1 := by rw [div_le_one hq0]; exact hqge
      linarith
    have hpos : (0 : ℝ) ≤ (P.card + 4) / (P.card + 5) := by positivity
    calc (4 : ℝ) / (((P.card + 1 : ℕ) : ℝ) + 4) = (P.card + 4) / (P.card + 5) * (4 / (P.card + 4)) := by
          push_cast; field_simp; ring
      _ ≤ (1 - 1 / (q : ℝ)) * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
          apply mul_le_mul hf ih' (by positivity)
          have : (0 : ℝ) < 1 / (q : ℝ) := by positivity
          have : 1 / (q : ℝ) < 1 := by rw [div_lt_one hq0]; linarith
          linarith

/-- `5 · 7 ⋯ (2t + 3)`. -/
def oddProd : ℕ → ℕ
  | 0 => 1
  | t + 1 => oddProd t * (2 * t + 5)

/-- `∏ p ≥ 5 · 7 ⋯ (2t + 3)` for `t` distinct odd `p ≥ 5`. -/
theorem prod_ge_oddProd (P : Finset ℕ) (hP : ∀ p ∈ P, 5 ≤ p ∧ p % 2 = 1) : oddProd P.card ≤ ∏ p ∈ P, p := by
  induction P using Finset.induction_on_max with
  | empty => simp [oddProd]
  | insert q P hlt ih =>
    have hqP : q ∉ P := fun h => lt_irrefl q (hlt q h)
    have hq := hP q (mem_insert_self _ _)
    have ih' := ih fun p hp => hP p (mem_insert_of_mem hp)
    rw [prod_insert hqP, card_insert_of_notMem hqP, oddProd]
    -- `q ≥ 2|P| + 5`: the elements of `P` are odd numbers in `[5, q)`
    have hcard : 2 * P.card + 5 ≤ q := by
      have hsub : P.image (fun p => (p - 5) / 2) ⊆ range ((q - 5) / 2) := by
        intro y hy
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
        have h1 := hP p (mem_insert_of_mem hp)
        have h2 := hlt p hp
        rw [mem_range]; omega
      have hinj : Set.InjOn (fun p => (p - 5) / 2) P := by
        intro x hx y hy hxy
        have h1 := hP x (mem_insert_of_mem hx)
        have h2 := hP y (mem_insert_of_mem hy)
        simp only at hxy
        omega
      have := card_le_card hsub
      rw [card_image_of_injOn hinj, card_range] at this
      omega
    calc oddProd P.card * (2 * P.card + 5) ≤ (∏ p ∈ P, p) * q := Nat.mul_le_mul ih' hcard
      _ = q * ∏ p ∈ P, p := mul_comm _ _

/-- The size of the window for `t ≥ 4` primes. -/
def win (t : ℕ) : ℕ := (t + 4) * 2 ^ (t - 3)

theorem oddProd_pos (t : ℕ) : 0 < oddProd t := by
  induction t with
  | zero => simp [oddProd]
  | succ t ih => simp only [oddProd]; positivity

/-- **The window fits.** For `t ≥ 4`: `24 (S² + S + 1) < 18 + 2 · 5 · 7 ⋯ (2t + 3)`, `S = (t + 4) 2^(t-3)`. -/
theorem win_fits (t : ℕ) (ht : 4 ≤ t) : 24 * (win t ^ 2 + win t + 1) < 18 + 2 * oddProd t := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    -- `S_{t+1} ≤ (5/2) S_t`, so the left side grows by at most `25/4 < 7`, the right side by `2t + 5 ≥ 13`
    have hw : 2 * win (t + 1) ≤ 5 * win t := by
      unfold win
      rw [show t + 1 - 3 = (t - 3) + 1 by omega, pow_succ]
      have : 0 < 2 ^ (t - 3) := by positivity
      nlinarith
    have hS : 1 ≤ win t := by
      unfold win
      have : 0 < 2 ^ (t - 3) := by positivity
      nlinarith
    have hO := oddProd_pos t
    have hO' : oddProd (t + 1) = oddProd t * (2 * t + 5) := rfl
    have h4 : 4 * (win (t + 1) ^ 2 + win (t + 1) + 1) ≤ 25 * (win t ^ 2 + win t + 1) := by nlinarith
    have : 13 * oddProd t ≤ oddProd t * (2 * t + 5) := by nlinarith
    nlinarith

/-! ### The shift -/

/-- Products of distinct primes dividing `N` divide `N`. -/
theorem prod_dvd_of_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) (hN : ∀ p ∈ P, p ∣ N) :
    ∏ p ∈ P, p ∣ N := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert q P hqP ih =>
    rw [prod_insert hqP]
    have hq := hP q (mem_insert_self _ _)
    have hcop : Nat.Coprime q (∏ p ∈ P, p) := by
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      exact (Nat.coprime_primes hq (hP p (mem_insert_of_mem hp))).mpr fun h => hqP (h ▸ hp)
    exact hcop.mul_dvd_of_dvd_of_dvd (hN q (mem_insert_self _ _))
      (ih (fun p hp => hP p (mem_insert_of_mem hp)) fun p hp => hN p (mem_insert_of_mem hp))

/-- **The shift of Kim–Kim–Oh, §4.** For `a > 72` even and every `b`, some `s` has
`24 (s² + |s| + 1) < a` and `p ∤ b + 18 s` for every prime `p ≥ 5` dividing `a - 18`. -/
theorem exists_shift (a b : ℤ) (ha : 72 < a) (heven : Even a) :
    ∃ s : ℤ, 24 * (s ^ 2 + |s| + 1) < a ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → (p : ℤ) ∣ a - 18 → ¬ (p : ℤ) ∣ b + 18 * s := by
  set N := (a - 18).natAbs with hN
  set P := N.primeFactors.filter (5 ≤ ·) with hPdef
  have hN0 : N ≠ 0 := Int.natAbs_ne_zero.mpr (by omega)
  have hmemP : ∀ p : ℕ, p.Prime → 5 ≤ p → (p : ℤ) ∣ a - 18 → p ∈ P := by
    intro p hp h5 hdvd
    simp only [hPdef, mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, Int.natCast_dvd.mp hdvd, hN0⟩, h5⟩
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
  have hP5 : ∀ p ∈ P, 5 ≤ p := fun p hp => (mem_filter.mp hp).2
  have hPodd : ∀ p ∈ P, 5 ≤ p ∧ p % 2 = 1 := fun p hp => by
    have := (hPprime p hp).eq_two_or_odd
    have := hP5 p hp
    omega
  have hPdvd : ∀ p ∈ P, p ∣ N := fun p hp => Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1
  have hP18 : ∀ p ∈ P, ¬ (p : ℤ) ∣ 18 := by
    intro p hp h
    have h' : p ∣ 18 := by exact_mod_cast h
    have h5 := hP5 p hp
    have : p ∣ 2 * 3 ^ 2 := by norm_num; exact h'
    rcases (Nat.Prime.dvd_mul (hPprime p hp)).mp this with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · have := Nat.le_of_dvd (by norm_num) ((hPprime p hp).dvd_of_dvd_pow h3); omega
  -- `2 ∏ P ≤ a - 18`
  have h2P : 2 * ∏ p ∈ P, p ≤ N := by
    have hdvd := prod_dvd_of_primes P hPprime N hPdvd
    have h2 : 2 ∣ N := by
      obtain ⟨k, hk⟩ := heven
      have : ((2 : ℕ) : ℤ) ∣ a - 18 := ⟨k - 9, by omega⟩
      exact Int.ofNat_dvd_left.mp this
    have hcop : Nat.Coprime 2 (∏ p ∈ P, p) := by
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      exact (Nat.coprime_primes Nat.prime_two (hPprime p hp)).mpr (by have := hP5 p hp; omega)
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (hcop.mul_dvd_of_dvd_of_dvd h2 hdvd)
  have hNa : (N : ℤ) = a - 18 := by rw [hN, Int.natAbs_of_nonneg (by omega)]
  -- reduce to a window `j < 2S + 1`, `s = j - S`
  have hwin : ∀ S : ℕ, 24 * (S ^ 2 + S + 1) < a →
      (∃ j < 2 * S + 1, ∀ p ∈ P, ¬ (p : ℤ) ∣ (b - 18 * S) + 18 * j) →
      ∃ s : ℤ, 24 * (s ^ 2 + |s| + 1) < a ∧
        ∀ p : ℕ, p.Prime → 5 ≤ p → (p : ℤ) ∣ a - 18 → ¬ (p : ℤ) ∣ b + 18 * s := by
    intro S hS ⟨j, hj, hgood⟩
    refine ⟨(j : ℤ) - S, ?_, fun p hp h5 hdvd => ?_⟩
    · have h1 : |(j : ℤ) - S| ≤ S := by rw [abs_le]; constructor <;> omega
      have h2 : ((j : ℤ) - S) ^ 2 ≤ (S : ℤ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith
    · have := hgood p (hmemP p hp h5 hdvd)
      intro h; apply this
      have e : b - 18 * (S : ℤ) + 18 * (j : ℤ) = b + 18 * ((j : ℤ) - S) := by ring
      rw [e]; exact h
  by_cases ht2 : P.card ≤ 2
  · -- three values
    refine hwin 1 (by norm_num; omega) (exists_good_union P hPprime _ 18 hP18 3 ?_)
    calc ∑ p ∈ P, (3 / p + if 3 % p = 0 then 0 else 1) ≤ ∑ _p ∈ P, 1 := by
          refine sum_le_sum fun p hp => ?_
          have h5 := hP5 p hp
          rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; simp
      _ < 2 * 1 + 1 := by simp; omega
  by_cases ht3 : P.card = 3
  · -- seven values; `a - 18 ≥ 2 · 5 · 7 · 9`
    have hprod := prod_ge_oddProd P hPodd
    rw [ht3] at hprod
    have h315 : oddProd 3 = 315 := by decide
    have hge : 630 ≤ N := by omega
    have hge' : (630 : ℤ) ≤ a - 18 := by rw [← hNa]; exact_mod_cast hge
    refine hwin 3 (by norm_num; omega) (exists_good_union P hPprime _ 18 hP18 7 ?_)
    calc ∑ p ∈ P, (7 / p + if 7 % p = 0 then 0 else 1) ≤ ∑ p ∈ P, (1 + if p = 5 then 1 else 0) := by
          refine sum_le_sum fun p hp => ?_
          have h5 := hP5 p hp
          by_cases hp5 : p = 5
          · subst hp5; simp
          · by_cases hp7 : p = 7
            · subst hp7; simp
            · have hp6 : p ≠ 6 := by rintro rfl; exact absurd (hPprime 6 hp) (by decide)
              rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; simp [hp5]
      _ = P.card + #(P.filter (· = 5)) := by
          rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_boole]; rfl
      _ < 2 * 3 + 1 := by
          have : #(P.filter (· = 5)) ≤ 1 := by
            calc #(P.filter (· = 5)) ≤ #({5} : Finset ℕ) :=
                  card_le_card fun x hx => by simp only [mem_filter] at hx; simp [hx.2]
              _ = 1 := card_singleton 5
          omega
  · -- `t ≥ 4`: the Legendre sieve on `2S + 1` values, `S = (t + 4) 2^(t-3)`
    have ht4 : 4 ≤ P.card := by omega
    set t := P.card with ht
    have hprod := prod_ge_oddProd P hPodd
    have hfit := win_fits t ht4
    have hge : 2 * oddProd t ≤ N := le_trans (Nat.mul_le_mul_left 2 hprod) h2P
    have hge' : ((2 * oddProd t : ℕ) : ℤ) ≤ a - 18 := by rw [← hNa]; exact_mod_cast hge
    have hfit' : ((24 * (win t ^ 2 + win t + 1) : ℕ) : ℤ) < ((18 + 2 * oddProd t : ℕ) : ℤ) := by
      exact_mod_cast hfit
    refine hwin (win t) (by push_cast at hge' hfit' ⊢; linarith) (exists_good P hPprime _ 18 hP18 _ ?_)
    have hge := prod_one_sub_inv_ge P hP5
    have ht0 : (0 : ℝ) < t + 4 := by positivity
    have h8 : (2 : ℝ) ^ t = 2 ^ (t - 3) * 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
    have hw : ((2 * win t + 1 : ℕ) : ℝ) * (4 / (t + 4)) = 2 ^ t + 4 / (t + 4) := by
      unfold win
      rw [h8]
      push_cast; field_simp; ring
    calc (2 : ℝ) ^ t < 2 ^ t + 4 / (t + 4) := by have : (0 : ℝ) < 4 / (t + 4) := by positivity
                                                 linarith
      _ = ((2 * win t + 1 : ℕ) : ℝ) * (4 / (t + 4)) := hw.symm
      _ ≤ ((2 * win t + 1 : ℕ) : ℝ) * ∏ p ∈ P, (1 - 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hge (by positivity)

end KimKimOh.Sieve

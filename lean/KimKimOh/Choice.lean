import KimKimOh.ScalarSlice
import KimKimOh.Windows
import KimKimOh.MaximalMod
import KimKimOh.Overlattice

/-!
# Choosing the two coefficients (`sec:high`)

Fix a decomposition `L ⊇ K ⊥ ⟨s⟩` with `det K = j`, a maximal ternary `S` in a reduced basis, and
`x ∈ {0, 1, 2, 3, 6}`. For `p ≥ 5` a correction passes the local test at `p` when it has rank
at least 2 modulo `p` or a diagonal entry in the square class of `j` (`OkAt`).

* `atMostClasses_one_not_okAt` (the claim of `sec:high`): once `y` avoids `a y ≡ b x` at the
  primes dividing `δ` but not `a`, and, for `x = 0`, satisfies the extra condition at the primes
  dividing `a` but not `c`, each prime `p ≥ 5` excludes at most one residue of `k`. Through the
  identity `a Δ = (a - s x²) δ - s (a y - b x)²`, a prime dividing both `δ` and `Δ` divides `a`
  and `b`, so `lem:scalar-slice` applies with `B ≡ 0` or `B' ≡ 0`, or the corrected second
  diagonal entry is in the square class of `j`.
-/

namespace KimKimOh

open Excluded

/-- The test of `lem:functional` at a prime `p ≥ 5`: rank at least 2 modulo `p`, or a diagonal
entry in the square class of `j`. -/
def Tern.OkAt (C : Tern) (j : ℤ) (p : ℕ) : Prop := C.RankGeTwoMod p ∨ C.HasDiagSquareClass j p

/-- Where the rank criterion fails on at most `ν` classes, so does the test of `lem:functional`. -/
theorem atMostClasses_not_okAt_of_rank {p ν : ℕ} {g : Tern} {s x y j : ℤ}
    (h : AtMostClasses p ν (fun k => (g.corr s x y k).RankLeOneMod p)) :
    AtMostClasses p ν (fun k => ¬ (g.corr s x y k).OkAt j p) := by
  intro ks hlen hpair
  obtain ⟨k, hk, hnb⟩ := h ks hlen hpair
  exact ⟨k, hk, fun hb => hb (Or.inl hnb)⟩

/-- `a Δ = (a - s x²) δ - s (a y - b x)²` (`eq:shared-prime`). -/
theorem a_mul_corrDelta (g : Tern) (s x y : ℤ) :
    g.a * g.corrDelta s x y = (g.a - s * x * x) * g.delta - s * (g.a * y - g.b * x) ^ 2 := by
  simp only [Tern.corrDelta, Tern.delta]; ring

/-- **The claim of `sec:high`.** -/
theorem atMostClasses_one_not_okAt {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {s : ℤ} (hs : s = 1 ∨ s = 2) (j : ℤ)
    (g : Tern) (x y : ℤ) (hG : g.NonzeroMod p)
    (hα : ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y)) (hx : (p : ℤ) ∣ x → x = 0)
    (hy : (p : ℤ) ∣ g.delta → (p : ℤ) ∣ g.a * y - g.b * x → (p : ℤ) ∣ g.a)
    (hx0 : x = 0 → (p : ℤ) ∣ g.a → ¬ (p : ℤ) ∣ g.c →
      (p : ℤ) ∣ g.c - s * y * y ∨
        ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (p : ℤ) ∣ (g.c - s * y * y) - j * u ^ 2) :
    AtMostClasses p 1 (fun k => ¬ (g.corr s x y k).OkAt j p) := by
  have hp := (Fact.out : p.Prime)
  have hBα : ¬ ((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c ∧ (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y) :=
    fun h => hα ⟨h.2.2.2.1, h.2.2.2.2⟩
  by_cases hδ : (p : ℤ) ∣ g.delta
  swap
  · exact atMostClasses_not_okAt_of_rank (scalar_slice_one hp5 hs g x y hG hBα (Or.inl hδ))
  by_cases hΔ : (p : ℤ) ∣ g.corrDelta s x y
  swap
  · -- no residue is excluded
    intro ks hlen _
    match ks, hlen with
    | [k₁, _], _ =>
      exact ⟨k₁, by simp, fun hb => hb (Or.inl (Tern.rankGeTwoMod_corr g s x y k₁ hΔ))⟩
  -- `p ∣ a y - b x`, hence `p ∣ a` and `p ∣ b`
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsq : (p : ℤ) ∣ s * (g.a * y - g.b * x) ^ 2 := by
    have e := a_mul_corrDelta g s x y
    have : (p : ℤ) ∣ (g.a - s * x * x) * g.delta - g.a * g.corrDelta s x y :=
      dvd_sub (dvd_mul_of_dvd_right hδ _) (dvd_mul_of_dvd_right hΔ _)
    rw [e] at this
    simpa using this
  have hs0 : ¬ (p : ℤ) ∣ s := by
    rcases hs with rfl | rfl
    · exact fun h => hpZ.not_dvd_one h
    · intro h
      have := Int.le_of_dvd (by norm_num) h
      omega
  have hayx : (p : ℤ) ∣ g.a * y - g.b * x :=
    hpZ.dvd_of_dvd_pow ((hpZ.dvd_or_dvd hsq).resolve_left hs0)
  have ha : (p : ℤ) ∣ g.a := hy hδ hayx
  have hb : (p : ℤ) ∣ g.b := by
    have : (p : ℤ) ∣ g.b * g.b := by
      have := dvd_sub (dvd_mul_of_dvd_left ha g.c) hδ
      simpa [Tern.delta] using this
    exact hpZ.dvd_of_dvd_pow (n := 2) (by rwa [sq])
  by_cases hx' : x = 0
  · subst hx'
    by_cases hc : (p : ℤ) ∣ g.c
    · exact atMostClasses_not_okAt_of_rank (scalar_slice_one hp5 hs g 0 y hG hBα (Or.inr (Or.inl ⟨ha, hb, hc⟩)))
    rcases hx0 rfl ha hc with h | ⟨u, hu, hcu⟩
    · refine atMostClasses_not_okAt_of_rank (scalar_slice_one hp5 hs g 0 y hG hBα (Or.inr (Or.inr ⟨?_, ?_, h⟩)))
      · simpa using ha
      · simpa using hb
    · -- the corrected second diagonal entry is in the square class of `j`
      intro ks hlen _
      match ks, hlen with
      | [k₁, _], _ =>
        refine ⟨k₁, by simp, fun hb => hb (Or.inr ⟨u, hu, Or.inr (Or.inl ?_)⟩)⟩
        simpa [Tern.corr] using hcu
  · -- `x ≠ 0`: then `p ∤ x`, and `p ∣ Δ ≡ -s c x²` gives `p ∣ c`
    have hpx : ¬ (p : ℤ) ∣ x := fun h => hx' (hx h)
    have hc : (p : ℤ) ∣ g.c := by
      have e : g.corrDelta s x y = -(s * x * x) * g.c + (g.a * g.c - g.b * g.b) +
          s * (2 * g.b * x * y - g.a * y * y) := by
        simp only [Tern.corrDelta, Tern.delta]; ring
      have h1 : (p : ℤ) ∣ (s * x * x) * g.c := by
        have e2 : (s * x * x) * g.c =
            g.delta + s * (2 * x * y * g.b - y * y * g.a) - g.corrDelta s x y := by
          rw [e]; simp only [Tern.delta]; ring
        rw [e2]
        exact dvd_sub (dvd_add hδ (dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hb _)
          (dvd_mul_of_dvd_right ha _)) _)) hΔ
      rcases hpZ.dvd_or_dvd h1 with h | h
      · rcases hpZ.dvd_or_dvd h with h | h
        · rcases hpZ.dvd_or_dvd h with h | h
          · exact absurd h hs0
          · exact absurd h hpx
        · exact absurd h hpx
      · exact h
    exact atMostClasses_not_okAt_of_rank (scalar_slice_one hp5 hs g x y hG hBα (Or.inr (Or.inl ⟨ha, hb, hc⟩)))

/-- **`eq:scalar-cost` gives the window of positive corrections.** Let `a, δ > 0`,
`3 δ² ≤ 4 a D`, `4 (a y - b x)² ≤ a² W²` and `s a² (3 W² + 4 d² g²) < 12 δ (a - s x²)`. Then
`Δ > 0` and `s (d g)² δ² < 4 D Δ`. -/
theorem cert_of_cost (g : Tern) {s x y : ℤ} (hs : 0 < s) (ha : 0 < g.a) (hδ : 0 < g.delta)
    (hh : 3 * g.delta ^ 2 ≤ 4 * g.a * g.det) {W M : ℤ}
    (hy : 4 * (g.a * y - g.b * x) ^ 2 ≤ g.a ^ 2 * W ^ 2)
    (hcost : s * g.a ^ 2 * (3 * W ^ 2 + 4 * M ^ 2) < 12 * g.delta * (g.a - s * x * x)) :
    0 < g.corrDelta s x y ∧ s * M ^ 2 * g.delta ^ 2 < 4 * g.det * g.corrDelta s x y := by
  have e := a_mul_corrDelta g s x y
  -- `4 a Δ ≥ 4 (a - s x²) δ - s a² W² > (4/3) s a² M²`
  have h4 : 3 * (4 * (g.a * g.corrDelta s x y)) > 4 * s * g.a ^ 2 * M ^ 2 := by
    rw [e]; nlinarith [mul_le_mul_of_nonneg_left hy hs.le]
  have hM : 0 ≤ s * g.a ^ 2 * M ^ 2 := by positivity
  have hΔ : 0 < g.corrDelta s x y := by
    by_contra hle
    push Not at hle
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le hle]
  refine ⟨hΔ, ?_⟩
  -- `3 Δ > s a M²`, and `4 a D ≥ 3 δ²`
  have h3 : 3 * g.corrDelta s x y > s * g.a * M ^ 2 := by
    by_contra hle
    push Not at hle
    nlinarith [mul_le_mul_of_nonneg_left hle ha.le]
  have := mul_le_mul_of_nonneg_right hh hΔ.le
  nlinarith [mul_lt_mul_of_pos_left h3 (by positivity : (0 : ℤ) < g.delta ^ 2), sq_nonneg g.delta]

/-- The local tests at 2 and 3 on progressions: for every `y ≡ y₀ (mod h)` there is a class of
`k` modulo `d` on which every correction is represented by `K` at 2 and at 3. -/
def LocalProgressions {κ : Type*} [Fintype κ] (K : GramLattice κ) (g : Tern) (s x : ℤ)
    (h d : ℕ) (y₀ : ℤ) : Prop :=
  ∀ y : ℤ, (h : ℤ) ∣ y - y₀ → ∃ k₀ : ℤ, ∀ k : ℤ, (d : ℤ) ∣ k - k₀ →
    LocallyRepresents K.gram (g.corr s x y k).toMatrix 2 ∧
      LocallyRepresents K.gram (g.corr s x y k).toMatrix 3

/-- The primes from 5 dividing a positive integer, as a finset. -/
def bigPrimesOf (n : ℤ) : Finset ℕ := n.natAbs.primeFactors.filter (5 ≤ ·)

theorem mem_bigPrimesOf {n : ℤ} (hn : n ≠ 0) {p : ℕ} :
    p ∈ bigPrimesOf n ↔ p.Prime ∧ 5 ≤ p ∧ (p : ℤ) ∣ n := by
  simp only [bigPrimesOf, Finset.mem_filter, Nat.mem_primeFactors, Int.natAbs_ne_zero]
  constructor
  · rintro ⟨⟨hp, hd, -⟩, h5⟩; exact ⟨hp, h5, Int.natCast_dvd.mpr hd⟩
  · rintro ⟨hp, h5, hd⟩; exact ⟨⟨hp, Int.natCast_dvd.mp hd, hn⟩, h5⟩

theorem card_bigPrimesOf_le {n : ℤ} (hn : 0 < n) {t : ℕ} (ht : n < Primes.P (t + 1)) :
    (bigPrimesOf n).card ≤ t :=
  Primes.card_le_of_lt_P (n := n.natAbs) (by omega) (by omega) _ fun p hp => by
    rw [mem_bigPrimesOf hn.ne'] at hp
    exact ⟨⟨hp.1, hp.2.1⟩, Int.natCast_dvd.mp hp.2.2⟩

/-- **`sec:high`: the two successive choices.** Let `S` be maximal in a reduced basis, and let
`x ∈ {0, 1, 2, 3, 6}`, steps `h, d ∣ 6` and a start `y₀` carry the local progressions at 2 and 3.
Let `P_t ≤ δ < P_{t+1}` (only the upper bound is used), `W = h g_t` (or `12` when `x = 0`, with a
signed divisor `y` of 6 in the progression satisfying the extra condition), and
`eq:scalar-cost`: `s a² (3 W² + 4 d² g_t²) < 12 δ (a - s x²)`. Then `L` represents `S`. -/
theorem represents_of_scalarCost {κ : Type*} [Fintype κ] (K : GramLattice κ) (j : ℤ) {s : ℤ} (hs : s = 1 ∨ s = 2)
    (hs0 : 0 < s)
    (hK : ∀ T : GramLattice (Fin 3), (∀ p : ℕ, p.Prime → LocallyRepresents K.gram T.gram p) →
      K.Represents T)
    (hloc : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ C : Tern, C.OkAt j p →
      LocallyRepresents K.gram C.toMatrix p)
    {ι : Type*} [Fintype ι] (L : GramLattice ι) (hL : L.Represents (K.orthSum (line s hs0)))
    (S : GramLattice (Fin 3)) (hmax : IsMaximal S.gram) (hred : (ternOf S).IsReduced)
    (x : ℤ) (hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 6)
    (h d : ℕ) (hh : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 6) (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6)
    (y₀ : ℤ) (hprog : LocalProgressions K (ternOf S) s x h d y₀)
    (t : ℕ) (ht : (ternOf S).delta < Primes.P (t + 1)) (W : ℤ)
    (hW : x ≠ 0 → W = h * Windows.gWin t)
    (hy0 : x = 0 → W = 12 ∧ ∃ y : ℤ, (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 6 ∨ y = -1 ∨ y = -2 ∨ y = -3 ∨
      y = -6) ∧ (h : ℤ) ∣ y - y₀ ∧ ∀ p : ℕ, p.Prime → 5 ≤ p → (p : ℤ) ∣ (ternOf S).a →
        ¬ (p : ℤ) ∣ (ternOf S).c → (p : ℤ) ∣ (ternOf S).c - s * y * y ∨
          ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (p : ℤ) ∣ ((ternOf S).c - s * y * y) - j * u ^ 2)
    (hcost : s * (ternOf S).a ^ 2 * (3 * W ^ 2 + 4 * (d * Windows.gWin t : ℤ) ^ 2) <
      12 * (ternOf S).delta * ((ternOf S).a - s * x * x)) :
    L.Represents S := by
  classical
  set g := ternOf S with hg
  have ha := a_pos S
  have hδ := delta_pos S
  have hD := det_pos S
  have hsymm : ∀ i j, S.gram i j = S.gram j i := fun i j => S.gram_comm i j
  have hG : ∀ p : ℕ, p.Prime → g.NonzeroMod p := fun p hp =>
    nonzeroMod_of_isMaximal hmax hsymm hp
  have h6 : ∀ {p : ℕ}, p.Prime → 5 ≤ p → ∀ {n : ℕ}, (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) → ¬ p ∣ n :=
    fun hp h5 n hn => not_dvd_of_dvd_two_three hp h5 (a := 1) (b := 1) (by
      rcases hn with rfl | rfl | rfl | rfl <;> norm_num)
  -- **Step 1: the choice of `y`**, with `4 (a y - b x)² ≤ a² W²`
  obtain ⟨y, hyprog, hyW, hysieve, hyx0⟩ : ∃ y : ℤ, (h : ℤ) ∣ y - y₀ ∧
      4 * (g.a * y - g.b * x) ^ 2 ≤ g.a ^ 2 * W ^ 2 ∧
      (∀ p : ℕ, p.Prime → 5 ≤ p → (p : ℤ) ∣ g.delta → (p : ℤ) ∣ g.a * y - g.b * x →
        (p : ℤ) ∣ g.a) ∧
      (x = 0 → (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 6 ∨ y = -1 ∨ y = -2 ∨ y = -3 ∨ y = -6) ∧
        ∀ p : ℕ, p.Prime → 5 ≤ p → (p : ℤ) ∣ g.a → ¬ (p : ℤ) ∣ g.c →
          (p : ℤ) ∣ g.c - s * y * y ∨
            ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (p : ℤ) ∣ (g.c - s * y * y) - j * u ^ 2) := by
    by_cases hx0 : x = 0
    · obtain ⟨hW12, y, hy6, hyh, hyc⟩ := hy0 hx0
      refine ⟨y, hyh, ?_, fun p hp h5 _ hdvd => ?_, fun _ => ⟨hy6, hyc⟩⟩
      · rw [hx0, hW12]
        have : y ^ 2 ≤ 36 := by rcases hy6 with h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num
        nlinarith [sq_nonneg g.a]
      · rw [hx0, mul_zero, sub_zero] at hdvd
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h' | h'
        · exact h'
        · exact absurd h' (not_dvd_of_divisor_six hp h5 hy6)
    · -- the `y`-sieve at the primes dividing `δ` but not `a`
      set Py := (bigPrimesOf g.delta).filter fun p : ℕ => ¬ (p : ℤ) ∣ g.a
      have hPy : ∀ p ∈ Py, Primes.IsQ p ∧ ¬ p ∣ h ∧ (p : ℤ) ∣ g.delta ∧ ¬ (p : ℤ) ∣ g.a := by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hb := (mem_bigPrimesOf hδ.ne').mp hp'.1
        exact ⟨⟨hb.1, hb.2.1⟩, h6 hb.1 hb.2.1 hh, hb.2.2, hp'.2⟩
      have hcard : Py.card ≤ t :=
        (Finset.card_filter_le _ _).trans (card_bigPrimesOf_le hδ ht)
      obtain ⟨y₁, hy₁, hcent⟩ := exists_centred_progression (A := g.a) (B := 2 * g.b * x)
        (h := (h : ℤ)) ha (by rcases hh with rfl | rfl | rfl | rfl <;> norm_num) y₀
        (Windows.gWin t)
      have hamc : ∀ p ∈ Py, AtMostClasses p 1 (fun y => (p : ℤ) ∣ g.a * y - g.b * x) := by
        intro p hp
        obtain ⟨hq, -, -, hpa⟩ := hPy p hp
        intro ks hlen hpair
        match ks, hlen, hpair with
        | [u, v], _, hpair =>
          simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at hpair
          by_contra hall
          simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
            exists_eq_left, not_or, not_not] at hall
          have : (p : ℤ) ∣ g.a * (u - v) := by
            have := dvd_sub hall.1 hall.2; convert this using 1; ring
          rcases (Nat.prime_iff_prime_int.mp hq.1).dvd_or_dvd this with h' | h'
          · exact hpa h'
          · exact hpair h'
      obtain ⟨i, hi, hgood⟩ := Windows.window_survivor' t Py (fun p hp => (hPy p hp).1) hcard
        (fun p y => (p : ℤ) ∣ g.a * y - g.b * x) hamc y₁ h (fun p hp => (hPy p hp).2.1)
      obtain ⟨c, hc⟩ := hy₁
      refine ⟨y₁ + h * i, ⟨c + i, by linear_combination hc⟩, ?_, fun p hp h5 hpδ hpy => ?_,
        fun h0 => absurd h0 hx0⟩
      · have := hcent i hi
        rw [hW hx0]
        have e : 2 * g.a * (y₁ + h * i) - 2 * g.b * x = 2 * (g.a * (y₁ + h * i) - g.b * x) := by
          ring
        rw [e, abs_mul, abs_two] at this
        have h2 : (2 * |g.a * (y₁ + h * i) - g.b * x|) ^ 2 ≤ (g.a * h * Windows.gWin t) ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
        rw [mul_pow, sq_abs] at h2
        nlinarith [h2]
      · by_contra hpa
        have hmem : p ∈ Py :=
          Finset.mem_filter.mpr ⟨(mem_bigPrimesOf hδ.ne').mpr ⟨hp, h5, hpδ⟩, hpa⟩
        exact hgood p hmem hpy
  -- **Step 2: the window of positive corrections**
  obtain ⟨k₁, hk₁⟩ := hprog y hyprog
  obtain ⟨hΔpos, hcert⟩ := cert_of_cost g hs0 ha hδ hred.height (W := W)
    (M := (d : ℤ) * Windows.gWin t) hyW hcost
  have hd0 : (0 : ℤ) < d := by rcases hd with rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨k₂, hk₂, hpos⟩ := exists_window g ha hδ hD hs0 (M := (d : ℤ)) hd0 k₁
    (Windows.gWin t) hcert
  -- **Step 3: the `k`-sieve at the primes dividing `Δ`**
  set Pk := bigPrimesOf (g.corrDelta s x y) with hPkdef
  have hPk : ∀ p ∈ Pk, Primes.IsQ p ∧ ¬ p ∣ d := fun p hp => by
    have hb := (mem_bigPrimesOf hΔpos.ne').mp hp
    exact ⟨⟨hb.1, hb.2.1⟩, h6 hb.1 hb.2.1 hd⟩
  have hcardk : Pk.card ≤ t :=
    card_bigPrimesOf_le hΔpos ((Tern.corrDelta_le g s x y hs0.le ha hδ).trans_lt ht)
  have hamck : ∀ p ∈ Pk, AtMostClasses p 1 (fun k => ¬ (g.corr s x y k).OkAt j p) := by
    intro p hp
    obtain ⟨hpp, h5, -⟩ := (mem_bigPrimesOf hΔpos.ne').mp hp
    have : Fact p.Prime := ⟨hpp⟩
    have hxd : x ≠ 0 → ¬ (p : ℤ) ∣ x := fun hx0 => not_dvd_of_divisor_six hpp h5 (by
      rcases hx with h | h | h | h | h
      · exact absurd h hx0
      all_goals simp [h])
    refine atMostClasses_one_not_okAt h5 hs j g x y (hG p hpp) ?_ ?_ (hysieve p hpp h5)
      (fun hx0 => (hyx0 hx0).2 p hpp h5)
    · rintro ⟨hpx, hpy⟩
      by_cases hx0 : x = 0
      · exact not_dvd_of_divisor_six hpp h5 (hyx0 hx0).1 hpy
      · exact hxd hx0 hpx
    · intro hpx
      by_contra hx0
      exact hxd hx0 hpx
  obtain ⟨i, hi, hgood⟩ := Windows.window_survivor' t Pk (fun p hp => (hPk p hp).1) hcardk
    (fun p k => ¬ (g.corr s x y k).OkAt j p) hamck k₂ d (fun p hp => (hPk p hp).2)
  -- **The embedding**
  obtain ⟨hCa, hCδ, hCD⟩ := hpos i hi
  have hloc23 := hk₁ (k₂ + d * i) (by
    obtain ⟨c, hc⟩ := hk₂; exact ⟨c + i, by linear_combination hc⟩)
  refine hL.trans (represents_of_corr K hK hs0 S x y (k₂ + d * i) hCa hCδ hCD fun p hp => ?_)
  rcases prime_cases hp with rfl | rfl | h5
  · exact hloc23.1
  · exact hloc23.2
  · refine hloc p hp h5 _ ?_
    by_cases hpk : p ∈ Pk
    · exact not_not.mp (hgood p hpk)
    · left
      refine Tern.rankGeTwoMod_corr g s x y _ fun hdvd => hpk ?_
      exact (mem_bigPrimesOf hΔpos.ne').mpr ⟨hp, h5, hdvd⟩

end KimKimOh

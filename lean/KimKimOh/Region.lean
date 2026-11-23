import KimKimOh.PassCheck
import KimKimOh.Compute.Region
import KimKimOh.Tables.Data.ChunkData

/-!
# The region of binary blocks left by `sec:high`

For `S` maximal in a reduced basis with `a ≥ 2`, let `P_t ≤ δ < P_{t+1}`.

* `t ≥ 27`: `represents_of_tail`.
* `a ≥ 73`: with `a₀ ∈ [73, 84]`, `a₀ ≡ a (mod 12)`, the class bounds give `L ⊇ S` if
  `classSkip a₀ t` (then `3 P_t > 4 H(a₀, t)²`) or `a > Acap a₀ t` (then `a > 4 H(a₀, t) / 3`)
  (`app:prescriptions`).
* Otherwise `L ⊇ S` once `δ` exceeds the bound `high` of the local cases of the block's chunks
  (`represents_of_high_lt` with `a₀ = a`).

The remaining blocks form the region `InRegion`, which the first pass enumerates. The bound of a
block is read from `hiTab a t`, one table per `(a, t)` indexed by the classes of the chunk masks
(`hiOf`), and capped at `P_{t+1}`.
-/

namespace KimKimOh

open GramLattice Tables Primes

/-! ### The products `P_t` -/

theorem P_eq {t : ℕ} (ht : t ≤ 28) : P t = Pc t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Windows.P_succ, ih (by omega), Pc, Pc, List.prod_take_succ _ _ (by simp [qList]; omega),
      q_eq_list (by simp [qList]; omega)]

theorem P_pos (t : ℕ) : 0 < P t := Finset.prod_pos fun i _ => (q_prime i).pos

theorem P_strictMono : StrictMono P := by
  refine strictMono_nat_of_lt_succ fun t => ?_
  rw [Windows.P_succ]
  have := P_pos t
  have := five_le_q t
  nlinarith

/-- Every positive integer lies in some `[P_t, P_{t+1})`. -/
theorem exists_P_interval {n : ℕ} (hn : 0 < n) : ∃ t, P t ≤ n ∧ n < P (t + 1) := by
  classical
  have hex : ∃ t, n < P t := ⟨n, by
    have : ∀ k, k < P k := fun k => by
      induction k with
      | zero => simp [P]
      | succ k ih =>
        have h : P k < P (k + 1) := P_strictMono (Nat.lt_succ_self k)
        show k + 1 < P (k + 1)
        omega
    exact this n⟩
  set t := Nat.find hex with htdef
  have ht : n < P t := Nat.find_spec hex
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0] at ht; simp [P] at ht; omega
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  refine ⟨u, ?_, by rw [show u + 1 = t by omega]; exact ht⟩
  have := Nat.find_min hex (show u < t by omega)
  omega

/-! ### The table of bounds per `(a, t)` -/

theorem packF_lt {w : ℕ} {v : ℕ → ℕ} : ∀ {n : ℕ}, (∀ i < n, v i < 2 ^ w) → packF w n v < 2 ^ (w * n)
  | 0, _ => by simp [packF]
  | n + 1, hv => by
    show packF w n v + (v n <<< (w * n)) < 2 ^ (w * (n + 1))
    have h1 := packF_lt (n := n) fun i hi => hv i (by omega)
    have h2 := hv n (by omega)
    rw [Nat.shiftLeft_eq, show w * (n + 1) = w * n + w by ring, pow_add]
    have : v n * 2 ^ (w * n) ≤ (2 ^ w - 1) * 2 ^ (w * n) := Nat.mul_le_mul_right _ (by omega)
    have h3 : (2 ^ w - 1) * 2 ^ (w * n) = 2 ^ (w * n) * 2 ^ w - 2 ^ (w * n) := by
      rw [Nat.sub_mul, one_mul, mul_comm]
    have h4 : 2 ^ (w * n) ≤ 2 ^ (w * n) * 2 ^ w := Nat.le_mul_of_pos_right _ (by positivity)
    omega

theorem packF_get {w : ℕ} {v : ℕ → ℕ} : ∀ {n : ℕ}, (∀ i < n, v i < 2 ^ w) → ∀ k < n,
    (packF w n v >>> (w * k)) &&& (2 ^ w - 1) = v k
  | 0, _, k, hk => by omega
  | n + 1, hv, k, hk => by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    show (packF w n v + (v n <<< (w * n))) / 2 ^ (w * k) % 2 ^ w = v k
    rw [Nat.shiftLeft_eq]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · have ih := packF_get (n := n) (fun i hi => hv i (by omega)) k hk
      rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod] at ih
      have e : v n * 2 ^ (w * n) = (v n * 2 ^ (w * (n - k - 1)) * 2 ^ w) * 2 ^ (w * k) := by
        rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
        congr 2
        have : k + 1 ≤ n := hk
        calc w * n = w * (n - k - 1 + 1 + k) := by congr 1; omega
          _ = w * (n - k - 1) + (w + w * k) := by ring
      rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
      exact ih
    · have hlt := packF_lt (n := k) (w := w) fun i hi => hv i (by omega)
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
      exact Nat.mod_eq_of_lt (hv k (by omega))

theorem Pc_lt : ∀ t < 28, Pc t < 2 ^ 160 := by decide

theorem hiEntry_le (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (ml2 ml3 : ℕ → List ℕ)
    (a t i₂ i₃ : ℕ) : hiEntry j s prof2 prof3 ml2 ml3 a t i₂ i₃ ≤ Pc (t + 1) :=
  min_le_right _ _

theorem pget_lt (tab blk : ℕ) : pget tab blk < 16 := by
  unfold pget
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

/-- **Reading the table.** -/
theorem hiOf_hiTab (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (ml2 ml3 : ℕ → List ℕ)
    {a t : ℕ} (ht : t < 27) (pi2 pi3 b c : ℕ) :
    hiOf (hiTab j s prof2 prof3 ml2 ml3 a t) pi2 pi3 a b c =
      hiEntry j s prof2 prof3 ml2 ml3 a t (pget pi2 (blk2 (a % 8) (b % 4) (c % 8)))
        (pget pi3 (blk3 (a % 9) (b % 9) (c % 9))) := by
  have h2 := pget_lt pi2 (blk2 (a % 8) (b % 4) (c % 8))
  have h3 := pget_lt pi3 (blk3 (a % 9) (b % 9) (c % 9))
  unfold hiOf hiTab
  rw [packF_get (fun i _ => (hiEntry_le _ _ _ _ _ _ _ _ _ _).trans_lt (Pc_lt _ (by omega))) _
    (by omega)]
  congr 1 <;> omega

end KimKimOh

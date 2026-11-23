import KimKimOh.Local.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Module

/-!
# Hensel's lemma for representations of quadratic forms

`LocallyRepresents K S p` asks for integer matrices `X` with `Xᵀ K X ≡ S (mod pᵏ)` for every
`k`. One Newton iteration produces them at every prime (the lifting in the proofs of
`lem:functional` and `lem:local-precision`).

* `hensel`: let `K` and `S` be symmetric integer matrices (neither needs to be unimodular),
  `q ≠ 0` and `s₀ ≥ 1`. If `Xᵀ K X ≡ S` modulo `q^s₀`, and modulo `2q^s₀` on the diagonal, and
  `Xᵀ K C ≡ 1 (mod q)` for some `C` (the functionals `(x_j, ·)` are independent modulo `q`),
  then `K` represents `S` modulo every power of `q`, provided `q^(s₀-1) Cᵀ K C` has even
  values. The Newton step: if `S - Xᵀ K X = qˢ F` with `F` symmetric of even diagonal, write
  `F = U + Uᵀ` (`halfUpper`) and replace `X` by `X + qˢ C U`.
* `hensel_two`: the dyadic case `q = 2`, `s₀ = 2`, with congruences modulo `4` off the diagonal
  and modulo `8` on it.
* `locallyRepresents_of_seed`: the odd case. A `Seed K T` over a commutative ring is a matrix
  `X` with `Xᵀ K X = T` together with a matrix `Y` with `Y K X = 1`. For an odd prime `p`, a
  seed modulo `p` gives a representation over `ℤ_p`: apply `hensel` to `2K` and `2T`, with
  `q = p`, `s₀ = 1` and `C = Yᵀ / 2`.
* `Seed.of_host`, `Seed.of_conj`: a seed in a sublattice `Pᵀ K P` is a seed in `K`, and a seed
  for `Pᵀ T P`, with `P` invertible, is a seed for `T` (compare `LocallyRepresents.of_host`).
-/

namespace KimKimOh.Local

open Matrix

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-! ### The Newton iteration -/

/-- The "upper half" of a square matrix: the strict upper triangle and half the diagonal.
For `F` symmetric with even diagonal, `halfUpper F + (halfUpper F)ᵀ = F`. -/
def halfUpper (F : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if i < j then F i j else if i = j then F i i / 2 else 0

theorem halfUpper_add_transpose (F : Matrix (Fin n) (Fin n) ℤ) (hF : Fᵀ = F)
    (hd : ∀ i, (2 : ℤ) ∣ F i i) : halfUpper F + (halfUpper F)ᵀ = F := by
  ext i j
  simp only [halfUpper, Matrix.add_apply, transpose_apply, of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne']
  · simp only [lt_self_iff_false, ite_false, ite_true]
    have := hd i
    omega
  · have h' : F j i = F i j := by rw [← transpose_apply F i j, hF]
    simp [h, not_lt.mpr h.le, h.ne', h']

/-- The expansion of `(X + c C U)ᵀ K (X + c C U)` for symmetric `K`. -/
theorem conj_add_expand (K : Matrix ι ι ℤ) (hK : Kᵀ = K) (X C : Matrix ι (Fin n) ℤ)
    (U : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) :
    (X + c • (C * U))ᵀ * K * (X + c • (C * U)) =
      Xᵀ * K * X + c • ((Xᵀ * K * C) * U) + c • (Uᵀ * (Xᵀ * K * C)ᵀ) +
        (c * c) • (Uᵀ * (Cᵀ * K * C) * U) := by
  simp only [transpose_add, transpose_smul, transpose_mul, hK, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, transpose_transpose]
  module

theorem diag_conj_eq_dot (M U : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (Uᵀ * M * U) i i = (fun j => U j i) ⬝ᵥ (M *ᵥ fun j => U j i) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- One Newton step: the error `Xᵀ K X - S` improves from `qˢ` (and `2qˢ` on the diagonal) to
`qˢ⁺¹` (and `2qˢ⁺¹`), and `Xᵀ K C ≡ 1 (mod q)` is kept. -/
theorem hensel_step (K : Matrix ι ι ℤ) (hK : Kᵀ = K) (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : Sᵀ = S) (C : Matrix ι (Fin n) ℤ) (q : ℤ) (hq : q ≠ 0) (s : ℕ) (hs : 1 ≤ s)
    (hpar : ∀ v : Fin n → ℤ, (2 : ℤ) ∣ q ^ (s - 1) * (v ⬝ᵥ ((Cᵀ * K * C) *ᵥ v)))
    (X : Matrix ι (Fin n) ℤ)
    (hC : ∀ i j, q ∣ (Xᵀ * K * C) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j)
    (hE : ∀ i j, q ^ s ∣ (Xᵀ * K * X) i j - S i j)
    (hD : ∀ i, 2 * q ^ s ∣ (Xᵀ * K * X) i i - S i i) :
    ∃ X' : Matrix ι (Fin n) ℤ,
      (∀ i j, q ∣ (X'ᵀ * K * C) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) ∧
      (∀ i j, q ^ (s + 1) ∣ (X'ᵀ * K * X') i j - S i j) ∧
      (∀ i, 2 * q ^ (s + 1) ∣ (X'ᵀ * K * X') i i - S i i) := by
  set c : ℤ := q ^ s with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ hq
  -- the error `S - Xᵀ K X = c • F`, with `F = U + Uᵀ`
  set F : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (S i j - (Xᵀ * K * X) i j) / c
  have hF : S - Xᵀ * K * X = c • F := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, F, of_apply]
    rw [Int.mul_ediv_cancel']
    have := hE i j
    rw [← dvd_neg]; simpa using this
  have hsymm : (Xᵀ * K * X)ᵀ = Xᵀ * K * X := by
    simp only [transpose_mul, transpose_transpose, hK, Matrix.mul_assoc]
  have hFt : Fᵀ = F := by
    ext i j
    simp only [transpose_apply, F, of_apply]
    rw [← transpose_apply S i j, hS, ← transpose_apply (Xᵀ * K * X) i j, hsymm]
  have hFd : ∀ i, (2 : ℤ) ∣ F i i := by
    intro i
    obtain ⟨m, hm⟩ := hD i
    refine ⟨-m, ?_⟩
    simp only [F, of_apply]
    have hm' : S i i - (Xᵀ * K * X) i i = c * (2 * -m) := by
      rw [hc]; linear_combination (-1 : ℤ) * hm
    rw [hm', Int.mul_ediv_cancel_left _ hc0]
  set U := halfUpper F
  have hFU : F = U + Uᵀ := (halfUpper_add_transpose F hFt hFd).symm
  -- `Xᵀ K C = 1 + q • N`
  set N : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => ((Xᵀ * K * C) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) / q
  have hN : Xᵀ * K * C = 1 + q • N := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, N, of_apply]
    rw [Int.mul_ediv_cancel' (hC i j)]
    ring
  set W := Uᵀ * (Cᵀ * K * C) * U
  refine ⟨X + c • (C * U), ?_, ?_⟩
  · intro i j
    have h : (X + c • (C * U))ᵀ * K * C = Xᵀ * K * C + c • (Uᵀ * (Cᵀ * K * C)) := by
      simp only [transpose_add, transpose_smul, transpose_mul, Matrix.add_mul,
        Matrix.smul_mul, Matrix.mul_assoc]
    rw [h, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h2 : q ∣ c := by rw [hc]; exact dvd_pow_self q (by omega)
    have e : (Xᵀ * K * C) i j + c * (Uᵀ * (Cᵀ * K * C)) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j
        = ((Xᵀ * K * C) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) +
          c * (Uᵀ * (Cᵀ * K * C)) i j := by ring
    rw [e]
    exact dvd_add (hC i j) (dvd_mul_of_dvd_left h2 _)
  have key : (X + c • (C * U))ᵀ * K * (X + c • (C * U)) - S =
      (q * c) • (N * U + (N * U)ᵀ) + (c * c) • W := by
    have hX : Xᵀ * K * X = S - c • F := by rw [← hF]; abel
    have hNt : (Xᵀ * K * C)ᵀ = 1 + q • Nᵀ := by
      rw [hN, transpose_add, transpose_one, transpose_smul]
    rw [conj_add_expand K hK, hX, hNt, hN, hFU]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, transpose_mul, smul_add]
    module
  have hentry : ∀ i j, ((X + c • (C * U))ᵀ * K * (X + c • (C * U))) i j - S i j =
      q * c * ((N * U) i j + (N * U) j i) + c * c * W i j := by
    intro i j
    have := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at this
    rw [this, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.add_apply,
      transpose_apply, smul_eq_mul, smul_eq_mul]
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [hentry, hc]
    exact ⟨(N * U) i j + (N * U) j i + q ^ t * W i j, by ring⟩
  · rw [hentry, hc]
    obtain ⟨w, hw⟩ := hpar (fun j => U j i)
    rw [show t + 1 - 1 = t by omega, ← diag_conj_eq_dot] at hw
    exact ⟨(N * U) i i + w, by linear_combination q ^ (t + 1) * q * hw⟩

/-- **Hensel's lemma**, for any modulus `q ≠ 0` and starting precision `s₀ ≥ 1`: if
`Xᵀ K X ≡ S` modulo `q^s₀`, and modulo `2q^s₀` on the diagonal, and `Xᵀ K C ≡ 1 (mod q)`, where
`q^(s₀-1) Cᵀ K C` has even values, then `K` represents `S` modulo every power of `q`. -/
theorem hensel (K : Matrix ι ι ℤ) (hK : Kᵀ = K) (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : Sᵀ = S) (q : ℤ) (hq : q ≠ 0) (s₀ : ℕ) (hs₀ : 1 ≤ s₀) (X C : Matrix ι (Fin n) ℤ)
    (hpar : ∀ v : Fin n → ℤ, (2 : ℤ) ∣ q ^ (s₀ - 1) * (v ⬝ᵥ ((Cᵀ * K * C) *ᵥ v)))
    (hE : ∀ i j, q ^ s₀ ∣ (Xᵀ * K * X) i j - S i j)
    (hD : ∀ i, 2 * q ^ s₀ ∣ (Xᵀ * K * X) i i - S i i)
    (hC : ∀ i j, q ∣ (Xᵀ * K * C) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) (k : ℕ) :
    ∃ X' : Matrix ι (Fin n) ℤ, ∀ i j, q ^ k ∣ (X'ᵀ * K * X') i j - S i j := by
  have main : ∀ m : ℕ, ∃ X' : Matrix ι (Fin n) ℤ,
      (∀ i j, q ∣ (X'ᵀ * K * C) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) ∧
      (∀ i j, q ^ (s₀ + m) ∣ (X'ᵀ * K * X') i j - S i j) ∧
      (∀ i, 2 * q ^ (s₀ + m) ∣ (X'ᵀ * K * X') i i - S i i) := by
    intro m
    induction m with
    | zero => exact ⟨X, hC, hE, hD⟩
    | succ m ih =>
      obtain ⟨X', h1, h2, h3⟩ := ih
      refine hensel_step K hK S hS C q hq (s₀ + m) (by omega) (fun v => ?_) X' h1 h2 h3
      rw [show s₀ + m - 1 = (s₀ - 1) + m by omega, pow_add, mul_right_comm]
      exact dvd_mul_of_dvd_left (hpar v) _
  obtain ⟨X', -, h2, -⟩ := main k
  exact ⟨X', fun i j => (pow_dvd_pow q (by omega)).trans (h2 i j)⟩

/-- **Dyadic Hensel lemma.** If `Xᵀ K X ≡ S` modulo `4` off the diagonal and modulo `8` on it,
and `Xᵀ K C ≡ 1 (mod 2)` for some `C`, then `K` represents `S` over `ℤ₂`. -/
theorem hensel_two (K : Matrix ι ι ℤ) (hK : Kᵀ = K) (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : Sᵀ = S) (X C : Matrix ι (Fin n) ℤ)
    (h4 : ∀ i j, (4 : ℤ) ∣ (Xᵀ * K * X) i j - S i j)
    (h8 : ∀ i, (8 : ℤ) ∣ (Xᵀ * K * X) i i - S i i)
    (hC : ∀ i j, (2 : ℤ) ∣ (Xᵀ * K * C) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) :
    LocallyRepresents K S 2 := fun k => by
  obtain ⟨X', h⟩ := hensel K hK S hS 2 (by norm_num) 2 (by norm_num) X C
    (fun v => dvd_mul_of_dvd_left (by norm_num) _) (by simpa using h4) (by simpa using h8)
    (by simpa using hC) k
  exact ⟨X', by simpa using h⟩

end KimKimOh.Local

namespace KimKimOh.Local.OddPrime

open Matrix

variable {ι κ μ : Type*}

/-! ### Seeds -/

section Seed

variable {R : Type*} [CommRing R] [Fintype ι]

/-- A seed for representing `T` by `K`: a matrix `X` with `Xᵀ K X = T` and a matrix `Y` with
`Y K X = 1`, so that `K X` has full column rank. -/
def Seed [DecidableEq κ] (K : Matrix ι ι R) (T : Matrix κ κ R) : Prop :=
  ∃ X : Matrix ι κ R, ∃ Y : Matrix κ ι R, Xᵀ * K * X = T ∧ Y * K * X = 1

variable [DecidableEq κ]

/-- A seed for `T` in `M = Pᵀ K P` gives a seed for `T` in `K`. -/
theorem Seed.of_host [Fintype μ] {K : Matrix ι ι R} {M : Matrix μ μ R} {T : Matrix κ κ R}
    (P : Matrix ι μ R) (hP : Pᵀ * K * P = M) (h : Seed M T) : Seed K T := by
  obtain ⟨X, Y, hX, hY⟩ := h
  refine ⟨P * X, Y * Pᵀ, ?_, ?_⟩
  · rw [← hX, ← hP, transpose_mul]
    simp only [Matrix.mul_assoc]
  · rw [← hY, ← hP]
    simp only [Matrix.mul_assoc]

/-- A seed for `Pᵀ T P`, where `P` has a right inverse, gives a seed for `T`. -/
theorem Seed.of_conj [Fintype κ] {K : Matrix ι ι R} {T : Matrix κ κ R} (P Q : Matrix κ κ R)
    (hPQ : P * Q = 1) (h : Seed K (Pᵀ * T * P)) : Seed K T := by
  obtain ⟨X, Y, hX, hY⟩ := h
  refine ⟨X * Q, P * Y, ?_, ?_⟩
  · calc (X * Q)ᵀ * K * (X * Q) = Qᵀ * (Xᵀ * K * X) * Q := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (P * Q)ᵀ * T * (P * Q) := by
          rw [hX, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = T := by rw [hPQ, transpose_one, Matrix.one_mul, Matrix.mul_one]
  · calc P * Y * K * (X * Q) = P * (Y * K * X) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hY, Matrix.mul_one, hPQ]

end Seed

/-! ### Congruences of integer matrices and `ZMod n` -/

/-- Entrywise congruence modulo `n` is equality after reduction to `ZMod n`. -/
theorem dvd_sub_iff_map_eq {n : ℕ} {A B : Matrix ι κ ℤ} :
    (∀ i j, (n : ℤ) ∣ A i j - B i j) ↔
      A.map (Int.castRingHom (ZMod n)) = B.map (Int.castRingHom (ZMod n)) := by
  constructor
  · intro h
    ext i j
    rw [map_apply, map_apply, eq_intCast, eq_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub,
      dvd_sub_comm]
    exact h i j
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [map_apply, eq_intCast] at this
    simpa [ZMod.intCast_eq_intCast_iff_dvd_sub] using this.symm

/-- The lift of a matrix over `ZMod n` to integer entries in `[0, n)`. -/
def liftZMod {n : ℕ} (A : Matrix ι κ (ZMod n)) : Matrix ι κ ℤ :=
  A.map fun x => (x.val : ℤ)

theorem map_liftZMod {n : ℕ} [NeZero n] (A : Matrix ι κ (ZMod n)) :
    (liftZMod A).map (Int.castRingHom (ZMod n)) = A := by
  ext i j
  simp [liftZMod]

theorem map_zsmul_cast {n : ℕ} (M : Matrix ι κ ℤ) (c : ℤ) :
    (c • M).map (Int.castRingHom (ZMod n)) = (c : ZMod n) • M.map (Int.castRingHom (ZMod n)) := by
  ext i j; simp

/-! ### Hensel's lemma at an odd prime -/

/-- **Hensel's lemma** with a seed modulo `p`: for an odd prime `p` and symmetric integer
matrices `K` and `T`, a seed for `T mod p` in `K mod p` gives a representation of `T` by `K`
over `ℤ_p`. Apply `hensel` to `2K` and `2T` with `q = p`, `s₀ = 1` and `C = Yᵀ / 2`. -/
theorem locallyRepresents_of_seed [Fintype ι] {n : ℕ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Matrix ι ι ℤ} {T : Matrix (Fin n) (Fin n) ℤ} (hK : Kᵀ = K) (hT : Tᵀ = T)
    (h : Seed (K.map (Int.castRingHom (ZMod p))) (T.map (Int.castRingHom (ZMod p)))) :
    LocallyRepresents K T p := by
  obtain ⟨X, Y, hX, hY⟩ := h
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hm1 : ((2 * (m + 1) : ℤ) : ZMod p) = 1 := by
    have : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by rw [← hm]; exact ZMod.natCast_self p
    push_cast at this ⊢; linear_combination this
  have h2p : IsCoprime (2 : ℤ) p := by
    have := Nat.isCoprime_iff_coprime.mpr
      ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr (Ne.symm hp2))
    exact_mod_cast this
  set X₀ := liftZMod X
  have h0 : ∀ i j, (p : ℤ) ∣ (X₀ᵀ * K * X₀) i j - T i j := by
    rw [dvd_sub_iff_map_eq]
    simp only [Matrix.map_mul, transpose_map, map_liftZMod, X₀, hX]
  have e2 (Z : Matrix ι (Fin n) ℤ) (i j : Fin n) :
      (Zᵀ * ((2 : ℤ) • K) * Z) i j - ((2 : ℤ) • T) i j = 2 * ((Zᵀ * K * Z) i j - T i j) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]; ring
  have hpar (C : Matrix ι (Fin n) ℤ) (v : Fin n → ℤ) :
      (2 : ℤ) ∣ (p : ℤ) ^ (1 - 1) * (v ⬝ᵥ ((Cᵀ * ((2 : ℤ) • K) * C) *ᵥ v)) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right 2 _) _
  intro k
  obtain ⟨X', hX'⟩ := hensel ((2 : ℤ) • K) (by rw [transpose_smul, hK]) ((2 : ℤ) • T)
    (by rw [transpose_smul, hT]) p hp0 1 le_rfl X₀ (((m + 1 : ℤ)) • (liftZMod Y)ᵀ)
    (hpar _)
    (fun i j => by rw [e2, pow_one]; exact dvd_mul_of_dvd_right (h0 i j) 2)
    (fun i => by rw [e2, pow_one]; exact mul_dvd_mul_left 2 (h0 i i))
    (by
      rw [dvd_sub_iff_map_eq]
      simp only [X₀, Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_zsmul_cast,
        Matrix.map_mul, transpose_map, map_liftZMod, Matrix.map_one _ (map_zero _) (map_one _)]
      have : Xᵀ * K.map (Int.castRingHom (ZMod p)) * Yᵀ = 1 := by
        rw [← transpose_one, ← hY]
        simp only [transpose_mul, ← transpose_map, hK, Matrix.mul_assoc]
      rw [this, mul_comm, hm1, one_smul])
    k
  exact ⟨X', fun i j => (h2p.symm.pow_left (m := k)).dvd_of_dvd_mul_left (e2 X' i j ▸ hX' i j)⟩

end KimKimOh.Local.OddPrime

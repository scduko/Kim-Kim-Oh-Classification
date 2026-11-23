import KimKimOh.Local.Hensel
import Mathlib.Algebra.Ring.GeomSum


/-!
# `lem:local-precision`

Let `J` be a diagonal Gram matrix of the quinary lattices at `p = 2` or `3`, and let `X` have
columns independent modulo `p`, in the form `Xᵀ Y ≡ 1 (mod p)` for some `Y`. If the norm
polynomials of `Xᵀ J X` and `C` agree modulo 8 at 2 or modulo 9 at 3, then `J` represents
`C` over `ℤ_p`.

* **At 2** the diagonal of `J` is odd, so `J ≡ 1 (mod 2)` and `Xᵀ J Y ≡ 1`. The dyadic Hensel
  lemma (`hensel_two`) applies directly (`locallyRepresents_of_precision_two`).
* **At 3** some diagonal entries are divisible by 3, and Hensel's lemma in the form of
  `KimKimOh.Local.hensel` does not apply. Instead, `J E = 3` for a symmetric `E` over
  `ZMod 3ᴷ` (`E = 3 J⁻¹`, integral because no entry of `J` is divisible by 9). The Newton step
  `X ↦ X + Δ` with `Δ = 3^(m-1) E Y W / 2` removes an error `3ᵐ W`, and leaves the error
  `-Δᵀ J Δ`, divisible by `3^(2m-1)` (`newton_step`). From `m = 2` the error vanishes in
  `ZMod 3ᴷ` after `K` steps (`exists_rep_zmod`, `locallyRepresents_of_precision_three`).

The paper argues by orthogonalization instead; the Newton step is the same estimate,
`(E Y W)ᵀ J (E Y W) = 3 Wᵀ Yᵀ E Y W`.
-/

namespace KimKimOh.Local.Precision

open Matrix KimKimOh.Local.OddPrime

variable {R : Type*} [CommRing R] {n m : ℕ}

/-- If `3ᴷ = 0`, then `1 + 3A` has a right inverse, the geometric series in `-3A`. -/
theorem exists_right_inv (K : ℕ) (h3 : (3 : R) ^ K = 0) (A : Matrix (Fin m) (Fin m) R) :
    ∃ S : Matrix (Fin m) (Fin m) R, (1 + (3 : R) • A) * S = 1 := by
  refine ⟨∑ i ∈ Finset.range K, ((-3 : R) • A) ^ i, ?_⟩
  have hg := mul_geom_sum ((-3 : R) • A) K
  have hK : ((-3 : R) • A) ^ K = 0 := by
    rw [smul_pow, neg_pow, h3, mul_zero, zero_smul]
  rw [hK, zero_sub] at hg
  have e : (1 + (3 : R) • A) = -((-3 : R) • A - 1) := by
    rw [neg_sub, neg_smul, sub_neg_eq_add, add_comm]
  rw [e, neg_mul, hg, neg_neg]

/-- **The Newton step at 3.** If `J E = 3`, `Xᵀ Y = 1` and `C - Xᵀ J X = 3ᵐ W` with `m ≥ 2`, then
`X' = X + 3^(m-1) E Y W / 2` has error `C - X'ᵀ J X'` divisible by `3^(m+1)` and still
`X'ᵀ Y ≡ 1 (mod 3)`. -/
theorem newton_step (J E : Matrix (Fin n) (Fin n) R) (hJ : Jᵀ = J) (hE : Eᵀ = E)
    (hJE : J * E = (3 : R) • 1) (i2 : R) (hi2 : 2 * i2 = 1) (C : Matrix (Fin m) (Fin m) R)
    (hC : Cᵀ = C) (X Y : Matrix (Fin n) (Fin m) R) (hXY : Xᵀ * Y = 1) (k : ℕ)
    (W : Matrix (Fin m) (Fin m) R) (hW : C - Xᵀ * J * X = (3 : R) ^ (k + 2) • W) :
    ∃ (X' : Matrix (Fin n) (Fin m) R) (W' B : Matrix (Fin m) (Fin m) R),
      C - X'ᵀ * J * X' = (3 : R) ^ (k + 3) • W' ∧ X'ᵀ * Y = 1 + (3 : R) • B := by
  set c : R := (3 : R) ^ (k + 1) * i2 with hc
  set V : Matrix (Fin n) (Fin m) R := E * Y * W with hV
  set Δ : Matrix (Fin n) (Fin m) R := c • V with hΔ
  -- the linear terms
  have hA : Xᵀ * J * V = (3 : R) • W := by
    calc Xᵀ * J * V = Xᵀ * (J * E) * Y * W := by simp only [hV, Matrix.mul_assoc]
      _ = (3 : R) • (Xᵀ * Y * W) := by
        rw [hJE]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = (3 : R) • W := by rw [hXY, Matrix.one_mul]
  have h1 : Xᵀ * J * Δ = (c * 3) • W := by rw [hΔ, Matrix.mul_smul, hA, smul_smul]
  have h2 : Δᵀ * J * X = (c * 3) • Wᵀ := by
    have : Δᵀ * J * X = (Xᵀ * J * Δ)ᵀ := by
      rw [transpose_mul, transpose_mul, transpose_transpose, hJ, Matrix.mul_assoc]
    rw [this, h1, transpose_smul]
  have hWt : (3 : R) ^ (k + 2) • Wᵀ = (3 : R) ^ (k + 2) • W := by
    rw [← transpose_smul, ← hW, transpose_sub, hC, transpose_mul, transpose_mul,
      transpose_transpose, hJ, Matrix.mul_assoc]
  have hc3 : c * 3 = i2 * (3 : R) ^ (k + 2) := by rw [hc]; ring
  have hlin : Xᵀ * J * Δ + Δᵀ * J * X = C - Xᵀ * J * X := by
    rw [h1, h2, hc3, ← smul_smul, ← smul_smul, ← smul_add, hWt, ← two_smul R, smul_smul,
      mul_comm i2 2, hi2, one_smul, hW]
  -- the quadratic term
  have hB : Vᵀ * J * V = (3 : R) • (Wᵀ * Yᵀ * E * Y * W) := by
    calc Vᵀ * J * V = Wᵀ * Yᵀ * E * (J * E) * Y * W := by
          rw [hV, transpose_mul, transpose_mul, hE]; simp only [Matrix.mul_assoc]
      _ = (3 : R) • (Wᵀ * Yᵀ * E * Y * W) := by
          rw [hJE]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  have h3 : Δᵀ * J * Δ = (c * c * 3) • (Wᵀ * Yᵀ * E * Y * W) := by
    rw [hΔ, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB,
      smul_smul]
  refine ⟨X + Δ, (-((3 : R) ^ k * i2 * i2)) • (Wᵀ * Yᵀ * E * Y * W),
    ((3 : R) ^ k * i2) • (Vᵀ * Y), ?_, ?_⟩
  · have hexp : (X + Δ)ᵀ * J * (X + Δ) =
        Xᵀ * J * X + (Xᵀ * J * Δ + Δᵀ * J * X) + Δᵀ * J * Δ := by
      rw [transpose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      abel
    rw [hexp, hlin, h3, smul_smul]
    have e : ∀ (A Q : Matrix (Fin m) (Fin m) R), C - (A + (C - A) + Q) = -Q := by
      intro A Q; abel
    rw [e, ← neg_smul]
    congr 1
    rw [hc]; ring
  · rw [transpose_add, Matrix.add_mul, hXY, hΔ, transpose_smul, Matrix.smul_mul, smul_smul]
    congr 2
    rw [hc]; ring

/-- **Newton's method at 3.** If `3ᴷ = 0`, `J E = 3`, `Xᵀ Y = 1` and `C ≡ Xᵀ J X` modulo 9,
then `J` represents `C` exactly. -/
theorem exists_rep_zmod (K : ℕ) (h3 : (3 : R) ^ K = 0) (J E : Matrix (Fin n) (Fin n) R)
    (hJ : Jᵀ = J) (hE : Eᵀ = E) (hJE : J * E = (3 : R) • 1) (i2 : R) (hi2 : 2 * i2 = 1)
    (C : Matrix (Fin m) (Fin m) R) (hC : Cᵀ = C) (X Y : Matrix (Fin n) (Fin m) R)
    (hXY : Xᵀ * Y = 1) (W : Matrix (Fin m) (Fin m) R) (hW : C - Xᵀ * J * X = (3 : R) ^ 2 • W) :
    ∃ X' : Matrix (Fin n) (Fin m) R, X'ᵀ * J * X' = C := by
  have step : ∀ N : ℕ, ∃ (X' Y' : Matrix (Fin n) (Fin m) R) (W' : Matrix (Fin m) (Fin m) R),
      X'ᵀ * Y' = 1 ∧ C - X'ᵀ * J * X' = (3 : R) ^ (N + 2) • W' := by
    intro N
    induction N with
    | zero => exact ⟨X, Y, W, hXY, hW⟩
    | succ N ih =>
      obtain ⟨X', Y', W', hXY', hW'⟩ := ih
      obtain ⟨X'', W'', B, hW'', hB⟩ :=
        newton_step J E hJ hE hJE i2 hi2 C hC X' Y' hXY' N W' hW'
      obtain ⟨S, hS⟩ := exists_right_inv K h3 B
      refine ⟨X'', Y' * S, W'', ?_, hW''⟩
      rw [← Matrix.mul_assoc, hB, hS]
  obtain ⟨X', -, W', -, hW'⟩ := step K
  refine ⟨X', ?_⟩
  rw [pow_add, h3, zero_mul, zero_smul, sub_eq_zero] at hW'
  exact hW'.symm

/-- `2` is invertible modulo `3ᴷ`. -/
theorem two_mul_inv (K : ℕ) : (2 : ZMod (3 ^ K)) * (((3 ^ K + 1) / 2 : ℕ) : ZMod (3 ^ K)) = 1 := by
  have hodd : (3 ^ K + 1) % 2 = 0 := by
    rw [Nat.add_mod, Nat.pow_mod]; norm_num
  have h : (2 * ((3 ^ K + 1) / 2) : ℕ) = 3 ^ K + 1 := by omega
  have := congrArg (fun t : ℕ => (t : ZMod (3 ^ K))) h
  push_cast at this
  have h3 : (3 : ZMod (3 ^ K)) ^ K = 0 := by exact_mod_cast ZMod.natCast_self (3 ^ K)
  rw [this, h3, zero_add]

/-- Integer entries divisible by `q` give a matrix `q • A`. -/
theorem exists_smul_of_dvd {ι κ : Type*} {q : ℤ} {M : Matrix ι κ ℤ} (h : ∀ i j, q ∣ M i j) :
    ∃ A : Matrix ι κ ℤ, M = q • A :=
  ⟨Matrix.of fun i j => M i j / q, by
    ext i j
    simp [Int.mul_ediv_cancel' (h i j)]⟩

/-- **`lem:local-precision` at 3.** Let `J` be symmetric with `J E = 3` for a symmetric `E` over
every `ZMod 3ᴷ`, let `Xᵀ Y ≡ 1 (mod 3)`, and let `C ≡ Xᵀ J X (mod 9)`. Then `J` represents `C`
over `ℤ₃`. -/
theorem locallyRepresents_of_precision_three (J : Matrix (Fin n) (Fin n) ℤ) (hJ : Jᵀ = J)
    (hE : ∀ K : ℕ, ∃ E : Matrix (Fin n) (Fin n) (ZMod (3 ^ K)), Eᵀ = E ∧
      J.map (Int.castRingHom (ZMod (3 ^ K))) * E = (3 : ZMod (3 ^ K)) • 1)
    (X Y : Matrix (Fin n) (Fin m) ℤ)
    (hY : ∀ i j, (3 : ℤ) ∣ (Xᵀ * Y - (1 : Matrix (Fin m) (Fin m) ℤ)) i j) (C : Matrix (Fin m) (Fin m) ℤ) (hC : Cᵀ = C)
    (h9 : ∀ i j, (9 : ℤ) ∣ (C - Xᵀ * J * X) i j) : LocallyRepresents J C 3 := by
  intro K
  set φ := Int.castRingHom (ZMod (3 ^ K))
  obtain ⟨E, hEs, hJE⟩ := hE K
  obtain ⟨A, hA⟩ := exists_smul_of_dvd hY
  obtain ⟨W, hW⟩ := exists_smul_of_dvd h9
  have h3 : (3 : ZMod (3 ^ K)) ^ K = 0 := by exact_mod_cast ZMod.natCast_self (3 ^ K)
  obtain ⟨S, hS⟩ := exists_right_inv K h3 (A.map φ)
  have hXY : (X.map φ)ᵀ * (Y.map φ) = 1 + (3 : ZMod (3 ^ K)) • A.map φ := by
    rw [← transpose_map, ← Matrix.map_mul, show Xᵀ * Y = 1 + (3 : ℤ) • A by rw [← hA]; abel]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      map_mul, map_ofNat]
    rcases eq_or_ne i j with rfl | h <;> simp [*]
  have hCW : C.map φ - (X.map φ)ᵀ * J.map φ * X.map φ = (3 : ZMod (3 ^ K)) ^ 2 • W.map φ := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_sub _ (map_sub φ), hW]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]
    norm_num
  obtain ⟨X', hX'⟩ := exists_rep_zmod K h3 (J.map φ) E (by rw [← transpose_map, hJ]) hEs hJE
    _ (two_mul_inv K) (C.map φ) (by rw [← transpose_map, hC]) (X.map φ) (Y.map φ * S)
    (by rw [← Matrix.mul_assoc, hXY, hS]) (W.map φ) hCW
  refine ⟨liftZMod X', ?_⟩
  have key := (dvd_sub_iff_map_eq (n := 3 ^ K) (A := (liftZMod X')ᵀ * J * liftZMod X')
    (B := C)).mpr (by
      simp only [Matrix.map_mul, transpose_map, map_liftZMod]
      exact hX')
  intro i j
  exact_mod_cast key i j

/-- **`lem:local-precision` at 2.** Let the diagonal of `J` be odd, let `Xᵀ Y ≡ 1 (mod 2)`, and
let `Xᵀ J X ≡ C` modulo 4, and modulo 8 on the diagonal. Then `J` represents `C` over `ℤ₂`. -/
theorem locallyRepresents_of_precision_two (J : Matrix (Fin n) (Fin n) ℤ) (hJ : Jᵀ = J)
    (hJ2 : ∀ i j, (2 : ℤ) ∣ J i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j)
    (X Y : Matrix (Fin n) (Fin m) ℤ)
    (hY : ∀ i j, (2 : ℤ) ∣ (Xᵀ * Y) i j - (1 : Matrix (Fin m) (Fin m) ℤ) i j)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : Cᵀ = C)
    (h4 : ∀ i j, (4 : ℤ) ∣ (Xᵀ * J * X) i j - C i j)
    (h8 : ∀ i, (8 : ℤ) ∣ (Xᵀ * J * X) i i - C i i) : LocallyRepresents J C 2 := by
  refine hensel_two J hJ C hC X Y h4 h8 fun i j => ?_
  have hsplit : (Xᵀ * J * Y) i j - (1 : Matrix (Fin m) (Fin m) ℤ) i j =
      (Xᵀ * (J - (1 : Matrix (Fin n) (Fin n) ℤ)) * Y) i j + ((Xᵀ * Y) i j - (1 : Matrix (Fin m) (Fin m) ℤ) i j) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.sub_apply]
    ring
  rw [hsplit]
  exact dvd_add (dvd_mul_mul_apply Xᵀ (J - (1 : Matrix (Fin n) (Fin n) ℤ)) Y (fun a b => by
    simpa [Matrix.sub_apply] using hJ2 a b) i j) (hY i j)

end KimKimOh.Local.Precision

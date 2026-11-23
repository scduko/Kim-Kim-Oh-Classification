import KimKimOh.Ternary
import KimKimOh.Maximal
import Mathlib.FieldTheory.ChevalleyWarning

/-!
# A maximal ternary is nonzero modulo every prime (§2, after `eq:maximal`)

If `G ≡ 0 (mod p)`, write `G = p G'`. By Chevalley–Warning the ternary quadratic form of `G'`
has a nonzero zero `x` modulo `p`; then `G x ≡ 0 (mod p)` and `xᵀ G x ≡ 0 (mod p²)`, so `x / p`
would give an integral enlargement. This is the paper's remark "At odd `p`, maximality implies
`G ≢ 0 (mod p)`", which the paper proves by diagonalizing `(G/p) mod p`. The Chevalley–Warning
argument also covers `p = 2`.
-/

namespace KimKimOh

open Matrix MvPolynomial

/-- Every ternary quadratic form over `ZMod p` has a nonzero zero (Chevalley–Warning). -/
theorem exists_isotropic_zmod (p : ℕ) [Fact p.Prime] (Q : Matrix (Fin 3) (Fin 3) (ZMod p)) :
    ∃ x : Fin 3 → ZMod p, x ≠ 0 ∧ ∑ i, ∑ j, x i * Q i j * x j = 0 := by
  classical
  set f : MvPolynomial (Fin 3) (ZMod p) := ∑ i, ∑ j, X i * C (Q i j) * X j
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have : f.totalDegree ≤ 2 := by
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      calc (X i * C (Q i j) * X j : MvPolynomial (Fin 3) (ZMod p)).totalDegree
          ≤ (X i * C (Q i j) : MvPolynomial (Fin 3) (ZMod p)).totalDegree +
              (X j : MvPolynomial (Fin 3) (ZMod p)).totalDegree := totalDegree_mul _ _
        _ ≤ ((X i : MvPolynomial (Fin 3) (ZMod p)).totalDegree +
              (C (Q i j) : MvPolynomial (Fin 3) (ZMod p)).totalDegree) +
              (X j : MvPolynomial (Fin 3) (ZMod p)).totalDegree :=
            Nat.add_le_add_right (totalDegree_mul _ _) _
        _ = 2 := by rw [totalDegree_X, totalDegree_C, totalDegree_X]
    simp only [Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions p hdeg
  have heval (x : Fin 3 → ZMod p) : eval x f = ∑ i, ∑ j, x i * Q i j * x j := by
    simp [f, map_sum]
  have h0 : (0 : Fin 3 → ZMod p) ∈ {x : Fin 3 → ZMod p | eval x f = 0} := by
    simp [heval]
  have hpos : 0 < Fintype.card {x : Fin 3 → ZMod p // eval x f = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, by simpa using h0⟩⟩
  have hge : 2 ≤ Fintype.card {x : Fin 3 → ZMod p // eval x f = 0} :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_of_dvd hpos hdvd)
  obtain ⟨⟨x, hx⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hge ⟨0, by simpa using h0⟩
  exact ⟨x, fun h => hne (Subtype.ext h), by rw [← heval]; exact hx⟩

/-- **A maximal ternary is nonzero modulo every prime.** -/
theorem nonzeroMod_of_isMaximal {G : Matrix (Fin 3) (Fin 3) ℤ} (hG : IsMaximal G)
    (hsym : ∀ i j, G i j = G j i) {p : ℕ} (hp : p.Prime) : (Tern.ofMatrix G).NonzeroMod p := by
  have := Fact.mk hp
  intro hall
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := hall
  -- every entry is divisible by `p`
  have hent (i j : Fin 3) : (p : ℤ) ∣ G i j := by
    fin_cases i <;> fin_cases j <;> simp [Tern.ofMatrix] at * <;>
      first | assumption | rwa [hsym]
  choose G' hG' using hent
  obtain ⟨x, hx0, hxQ⟩ := exists_isotropic_zmod p (Matrix.of fun i j => (G' i j : ZMod p))
  set y : Fin 3 → ℤ := fun i => ((x i).val : ℤ)
  refine hG p hp y ?_ ?_ ?_
  · by_contra hall
    push Not at hall
    apply hx0
    funext i
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hall i)
    simpa [y] using this
  · intro i
    have hGs : G = (p : ℤ) • Matrix.of G' := by ext a b; simp [hG' a b]
    rw [hGs, smul_mulVec, Pi.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  · have hGs : G = (p : ℤ) • Matrix.of G' := by ext a b; simp [hG' a b]
    rw [hGs, smul_mulVec, dotProduct_smul, smul_eq_mul, pow_two]
    refine mul_dvd_mul_left _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_)
    rw [← hxQ]
    simp [dotProduct, mulVec, Fin.sum_univ_three, y]
    ring

/-! ### Maximality at 2 -/

/-- Every ternary residue modulo 4 with `det ≡ 0 (mod 4)` has a vector `z ∈ {0,1}³ \ {0}` with
`G z ≡ 0 (mod 2)` and `zᵀ G z ≡ 0 (mod 4)` (a finite check over the 4096 residues). -/
theorem four_dvd_det_check : ∀ a b c d e f : ZMod 4,
    a * c * f + 2 * b * d * e - a * e * e - c * d * d - f * b * b = 0 →
    ∃ z ∈ ([(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)] :
        List (ZMod 4 × ZMod 4 × ZMod 4)),
      (2 * (a * z.1 + b * z.2.1 + d * z.2.2) = 0 ∧ 2 * (b * z.1 + c * z.2.1 + e * z.2.2) = 0 ∧
        2 * (d * z.1 + e * z.2.1 + f * z.2.2) = 0) ∧
      a * z.1 * z.1 + c * z.2.1 * z.2.1 + f * z.2.2 * z.2.2 +
        2 * (b * z.1 * z.2.1 + d * z.1 * z.2.2 + e * z.2.1 * z.2.2) = 0 := by
  decide

/-- **A maximal ternary has `4 ∤ det` (§2).** Otherwise `four_dvd_det_check` gives `z` with
`G z ≡ 0 (mod 2)` and `zᵀ G z ≡ 0 (mod 4)`, and `z / 2` is an integral enlargement. -/
theorem not_four_dvd_det_of_isMaximal {G : Matrix (Fin 3) (Fin 3) ℤ} (hG : IsMaximal G)
    (hsym : ∀ i j, G i j = G j i) : ¬ (4 : ℤ) ∣ (Tern.ofMatrix G).det := by
  intro h4
  set g := Tern.ofMatrix G
  have hdet : ((g.det : ℤ) : ZMod 4) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h4
  simp only [Tern.det, Tern.delta] at hdet
  push_cast at hdet
  obtain ⟨z, hz, ⟨h1, h2, h3⟩, hQ⟩ := four_dvd_det_check (g.a : ZMod 4) g.b g.c g.d g.e g.f
    (by linear_combination hdet)
  -- the integer vector with entries `0, 1`
  obtain ⟨y, hy, hyz⟩ : ∃ y : Fin 3 → ℤ, (∃ i, ¬ (2 : ℤ) ∣ y i) ∧
      ((y 0 : ZMod 4), (y 1 : ZMod 4), (y 2 : ZMod 4)) = z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨![1, 0, 0], ⟨0, by decide⟩, by simp⟩
    · exact ⟨![0, 1, 0], ⟨1, by decide⟩, by simp⟩
    · exact ⟨![0, 0, 1], ⟨2, by decide⟩, by simp⟩
    · exact ⟨![1, 1, 0], ⟨0, by decide⟩, by simp⟩
    · exact ⟨![1, 0, 1], ⟨0, by decide⟩, by simp⟩
    · exact ⟨![0, 1, 1], ⟨1, by decide⟩, by simp⟩
    · exact ⟨![1, 1, 1], ⟨0, by decide⟩, by simp⟩
  subst hyz
  have hG' : G = g.toMatrix := (Tern.toMatrix_ofMatrix (by
    ext i j; exact hsym j i)).symm
  refine hG 2 Nat.prime_two y hy (fun i => ?_) ?_
  · -- `2 (G y)ᵢ ≡ 0 (mod 4)`
    have key : ∀ m : ℤ, ((2 * m : ℤ) : ZMod 4) = 0 → (2 : ℤ) ∣ m := fun m hm => by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hm
      omega
    rw [hG']
    refine key _ ?_
    fin_cases i <;>
      simp [mulVec, dotProduct, Fin.sum_univ_three, Tern.toMatrix] <;>
      first
        | (linear_combination h1) | (linear_combination h2) | (linear_combination h3)
  · rw [hG', show ((2 : ℕ) : ℤ) ^ 2 = ((4 : ℕ) : ℤ) by norm_num,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [dotProduct, mulVec, Fin.sum_univ_three, Tern.toMatrix]
    simp
    linear_combination hQ

end KimKimOh

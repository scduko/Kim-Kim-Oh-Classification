import KimKimOh.Genus.K3K9
import KimKimOh.Bridge.Transfer
import QuadFormsKB.Siegel.NeighborGenus

/-!
# The genus of `K₂₂ = ⟨1, 1, 2⟩ ⊥ A₂`: two classes

`K₂₂ = ⟨1, 1, 2⟩ ⊥ A₂` (Kim–Kim–Oh's `K₂₂`, our `kko112`) and `K₆ = I₄ ⊥ ⟨6⟩`, with Gram matrices
`g22 = sumI (A₂ ⊥ ⟨2⟩) 2` and `k6 = sumI ⟨6⟩ 4`.

* The 2-adic symbol of `K₂₂` is `1^{-4}_2 2^{+1}_1` and its 3-adic symbol `1^{+4}3^{-1}`; the local
  masses are `m₂ = 2/3`, `m₃ = 729/256`, and the Conway–Sloane mass formula gives
  `mass(K₂₂) = 5/768` (`mass_g22`).
* `|Aut K₂₂| = 2²·2!·24 = 192` and `|Aut K₆| = 2⁴·4!·2 = 768` (vines, `card_aut_sumI`).
* `K₂₂` and `K₆` are in one genus (`sameGenus_g22_k6`): integral matrices `A₂`, `A₃` with
  `A₂ᵀ K₂₂ A₂ = 4 K₆` and `A₃ᵀ K₂₂ A₃ = 9 K₆`, together with inverses up to `4` and `9`, give the
  equivalences over every `ℤ_p` (`p ≠ 2` from `A₂`, `p = 2` from `A₃`) and over `ℝ`
  (`isometricGL_of_scaled`). `A₂` comes from a 2-neighbour of `K₆` isometric to `K₂₂`.
* `K₂₂ ≇ K₆`: three orthogonal unit vectors of `K₆` would map to vectors of `K₂₂` supported on its
  `I₂`, whose sum has norm `3`, not a sum of two squares (`not_intEquiv_g22_k6`).
* `1/192 + 1/768 = 5/768`, so the genus is `{K₂₂, K₆}` (`genusClasses_eq_of_sum_eq_mass`), and a
  form represented by `K₂₂` over every `ℤ_p` is represented by `K₂₂` or by `K₆`
  (`rep_g22_or_k6`).
-/

open Matrix

namespace KimKimOh.Genera

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass QuadFormsKB.Siegel.Kneser

/-! ### The Gram matrices -/

/-- `A₂ ⊥ ⟨2⟩`. -/
def a22 : Matrix (Fin 3) (Fin 3) ℤ := !![2, -1, 0; -1, 2, 0; 0, 0, 2]

/-- `⟨6⟩`. -/
def a6 : Matrix (Fin 1) (Fin 1) ℤ := !![6]

/-- `K₂₂ = A₂ ⊥ ⟨2⟩ ⊥ I₂`. -/
def g22 : Matrix (Fin 5) (Fin 5) ℤ := sumI a22 2

/-- `K₆ = ⟨6⟩ ⊥ I₄`. -/
def k6 : Matrix (Fin 5) (Fin 5) ℤ := sumI a6 4

theorem g22_eq : g22 = !![2, -1, 0, 0, 0; -1, 2, 0, 0, 0; 0, 0, 2, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem k6_eq : k6 = !![6, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem g22_symm : g22.IsSymm := by
  rw [g22_eq]; exact Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl

theorem k6_symm : k6.IsSymm := by
  rw [k6_eq]; exact Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl

theorem g22_det : g22.det = 6 := by
  rw [g22_eq]; simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem eval_g22 (x : Fin 5 → ℤ) : (ofMatrixZ g22).eval x =
    2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 + 2 * x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 := by
  rw [eval_ofMatrixZ, g22_eq]
  simp [dotProduct, mulVec, Fin.sum_univ_five]
  ring

theorem eval_k6 (x : Fin 5 → ℤ) : (ofMatrixZ k6).eval x =
    6 * x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 := by
  rw [eval_ofMatrixZ, k6_eq]
  simp [dotProduct, mulVec, Fin.sum_univ_five]
  ring

theorem posDef_g22 : IntQF.PosDef (ofMatrixZ g22) := by
  intro x hx
  rw [eval_g22]
  by_contra h
  apply hx
  have key : x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 + 2 * x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 ≤ 0 := by
    have e : x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 + 2 * x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 =
        2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 + 2 * x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 := by ring
    rw [e]; exact not_lt.mp h
  have p0 := sq_nonneg (x 0); have p1 := sq_nonneg (x 1); have p01 := sq_nonneg (x 0 - x 1)
  have p2 := sq_nonneg (x 2); have p3 := sq_nonneg (x 3); have p4 := sq_nonneg (x 4)
  have z : ∀ t : ℤ, t ^ 2 ≤ 0 → t = 0 := fun t ht => pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm ht (sq_nonneg t))
  have h0 := z (x 0) (by linarith); have h1 := z (x 1) (by linarith); have h2 := z (x 2) (by linarith)
  have h3 := z (x 3) (by linarith); have h4 := z (x 4) (by linarith)
  funext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]

/-! ### The 2-adic symbol -/

/-- `1^{-4}_2 2^{+1}_1`, the 2-adic symbol of `A₂ ⊥ ⟨2⟩ ⊥ I₂`. -/
def tau22 : TwoSymbol := fun k =>
  if k = 0 then ⟨4, .minus, .I, 2⟩ else if k = 1 then ⟨1, .plus, .I, 1⟩ else TwoFactor.trivial

/-- The block decomposition `(2x²+2xy+2y²) ⊥ ⟨2⟩ ⊥ ⟨1⟩ ⊥ ⟨1⟩` of `A₂ ⊥ ⟨2⟩ ⊥ I₂` over `ℤ₂`. -/
def blocks22 : List Cassels.DyBlock := [.ell 0, .sq 1 1, .sq 0 1, .sq 0 1]

/-- The block matrix of `blocks22`. -/
def gb22 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, 1, 0, 0, 0; 1, 2, 0, 0, 0; 0, 0, 2, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem flip_g22 : flipᵀ * g22 * flip = gb22 := by rw [g22_eq]; decide

theorem mat_sq1 (u : ℤ) : (Cassels.DyBlock.sq 1 u).mat = (!![2 * u] : Matrix (Fin 1) (Fin 1) ℤ).map Int.cast := by
  show (!![(2 : ℚ_[2]) ^ (1 : ℤ) * (u : ℚ_[2])] : Matrix (Fin 1) (Fin 1) ℚ_[2]) =
    (!![2 * u] : Matrix (Fin 1) (Fin 1) ℤ).map Int.cast
  ext i j; fin_cases i; fin_cases j; simp

/-- `blocks22` as an integral block matrix. -/
def ib22 : Matrix (Fin 5) (Fin 5) ℤ := Cassels.orthSumMat !![2, 1; 1, 2]
  (Cassels.orthSumMat !![2 * 1] (Cassels.orthSumMat !![1] (Cassels.orthSumMat !![1] (0 : Matrix (Fin 0) (Fin 0) ℤ))))

theorem ib22_eq : ib22 = gb22 := by decide

theorem dyMat_blocks22_eq : Cassels.dyMat blocks22 = ib22.map Int.cast := by
  show Cassels.orthSumMat _ (Cassels.orthSumMat _ (Cassels.orthSumMat _ (Cassels.orthSumMat _ 0))) = _
  rw [ib22, map_orthSumMat, map_orthSumMat, map_orthSumMat, map_orthSumMat, map_zero_fin0, mat_ell0, mat_sq1,
    mat_sq0]
  rfl

theorem dyMat_blocks22 :
    (Cassels.dyMat blocks22).submatrix (Fin.cast rfl) (Fin.cast rfl) = gb22.map (Int.cast : ℤ → ℚ_[2]) := by
  rw [dyMat_blocks22_eq, ib22_eq]; rfl

theorem isTwoSymbolOf_g22 : IsTwoSymbolOf (g22.map (Int.cast : ℤ → ℚ_[2])) tau22 := by
  refine ⟨blocks22, ?_, ?_, rfl, ?_, ?_⟩
  · intro b hb
    simp only [blocks22, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [Cassels.DyBlock.Valid]
  · intro b hb
    simp only [blocks22, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [blockExp]
  · have h := zpEquiv_of_int 2 flip flip_det flip_g22
    rw [← dyMat_blocks22] at h
    exact h
  · funext k
    rcases k with _ | _ | k
    · simp only [tau22, ite_true, blockSymbol, blocks22]
      decide
    · simp only [tau22, blockSymbol, blocks22]
      decide
    · have hf : List.filter (fun b => decide (blockExp b = ((k + 1 + 1 : ℕ) : ℤ))) blocks22 = [] := by
        simp [blocks22, blockExp]; omega
      show (if k + 1 + 1 = 0 then _ else if k + 1 + 1 = 1 then _ else TwoFactor.trivial) = blockSymbol blocks22 _
      rw [ite_eq_right (by omega : k + 1 + 1 ≠ 0), ite_eq_right (by omega : k + 1 + 1 ≠ 1)]
      unfold blockSymbol
      simp only [hf]
      rfl

/-! ### The 3-adic symbol -/

/-- `1^{+4}3^{-1}`, the 3-adic symbol of `A₂ ⊥ ⟨2⟩ ⊥ I₂`. -/
def sig22 : OddSymbol := fun k => if k = 0 then ⟨4, .plus⟩ else if k = 1 then ⟨1, .minus⟩ else OddFactor.trivial

theorem T3_g22 : T3ᵀ * g22 * T3 = Matrix.diagonal ![2, 6, 2, 1, 1] := by rw [g22_eq]; decide

/-- The unit parts. -/
noncomputable def u22 : Fin 5 → ℚ_[3] := ![2, 2, 2, 1, 1]

theorem norm_u22 (i : Fin 5) : ‖u22 i‖ = 1 := by
  fin_cases i <;> simp [u22, norm_two_padic_three]

theorem isSquare_four_padic_three : IsSquare (4 : ℚ_[3]) := ⟨2, by norm_num⟩

theorem isOddSymbolOf_g22 : IsOddSymbolOf 3 (g22.map (Int.cast : ℤ → ℚ_[3])) sig22 := by
  refine ⟨![0, 1, 0, 0, 0], u22, norm_u22, ?_, ?_⟩
  · have e : (Matrix.diagonal fun i => ((3 : ℕ) : ℚ_[3]) ^ ((![0, 1, 0, 0, 0] : Fin 5 → ℕ) i) * u22 i) =
        (Matrix.diagonal ![2, 6, 2, 1, 1] : Matrix (Fin 5) (Fin 5) ℤ).map (Int.cast : ℤ → ℚ_[3]) := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [u22, Matrix.diagonal]
    rw [e]
    exact zpEquiv_of_int 3 T3 T3_det T3_g22
  · funext k
    rcases k with _ | _ | k
    · have hp : (∏ i : {i : Fin 5 // (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i = 0}, u22 i) = 4 := by
        rw [← Finset.prod_subtype ({0, 2, 3, 4} : Finset (Fin 5)) (by decide) u22]
        simp [u22, Finset.prod_insert]; norm_num
      simp only [sig22, oddSymbolOfDiag, ite_true, hp, isSquare_four_padic_three, OddFactor.mk.injEq, and_true]
      rw [Fintype.card_subtype]; decide
    · have hp : (∏ i : {i : Fin 5 // (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i = 0 + 1}, u22 i) = 2 := by
        rw [← Finset.prod_subtype ({1} : Finset (Fin 5)) (by decide) u22]
        simp [u22]
      simp only [sig22, oddSymbolOfDiag, show (0 + 1 : ℕ) ≠ 0 by omega, ite_false, ite_true, hp,
        not_isSquare_two_padic_three, OddFactor.mk.injEq, and_true]
      rw [Fintype.card_subtype]; decide
    · have he : ∀ i : Fin 5, (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i ≠ k + 1 + 1 := by
        intro i; fin_cases i <;> simp
      have : IsEmpty {i : Fin 5 // (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i = k + 1 + 1} := ⟨fun ⟨i, hi⟩ => he i hi⟩
      have hsq : IsSquare (∏ i : {i : Fin 5 // (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i = k + 1 + 1}, u22 i) := by
        rw [Finset.univ_eq_empty, Finset.prod_empty]; exact ⟨1, (mul_one 1).symm⟩
      simp only [sig22, oddSymbolOfDiag, show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ite_false,
        OddFactor.trivial, hsq, ite_true, OddFactor.mk.injEq, and_true]
      symm
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => he i hi⟩

/-! ### The local masses and the mass -/

theorem pMassTwo_tau22 : pMassTwo tau22 2 = 2 / 3 := by
  have hd : diagProdTwo tau22 2 = 1 / 12 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, tau22, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (tau22 k).dim) 2 = 4 := by decide
  have hII : nII tau22 2 = 0 := by decide
  have hII' : nII' tau22 2 = 1 := by decide
  have h2 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  rw [pMassTwo, hd, hc, hII, hII', h2]; norm_num

theorem pMassOdd_sig22 : pMassOdd 3 sig22 2 = 729 / 256 := by
  have hd : (∏ k ∈ Finset.range 2, (oddSpecies 3 (sig22 k)).diagFactor 3) = 81 / 256 := by
    simp [sig22, Finset.prod_range_succ, oddSpecies, Species.diagFactor, lowerProd, Sign.flip, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (sig22 k).dim) 2 = 4 := by decide
  have h3 : Real.sqrt 3 ^ 4 = 9 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  rw [pMassOdd, hd, hc]; push_cast; rw [h3]; norm_num

theorem primeFactors_twelve : (2 * (6 : ℤ)).natAbs.primeFactors = {2, 3} := by
  rw [show (2 * (6 : ℤ)).natAbs = 2 ^ 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  rfl

/-- **The mass of the genus of `K₂₂` is `5/768`** (Conway–Sloane mass formula). -/
theorem mass_g22 : Siegel.mass (ofMatrixZ g22) = 5 / 768 := by
  have hsupp2 : tau22.SupportedBelow 2 := fun k hk => by
    simp [tau22, show k ≠ 0 by omega, show k ≠ 1 by omega]
  have hsupp3 : ∀ k, 2 ≤ k → sig22 k = OddFactor.trivial := fun k hk => by
    simp [sig22, show k ≠ 0 by omega, show k ≠ 1 by omega]
  rw [mass_eq_stdMass_mul_symbols_unconditional (by norm_num) g22_symm posDef_g22 tau22 2
    isTwoSymbolOf_g22 hsupp2 (fun _ => sig22) (fun _ => 2) ?_]
  · rw [g22_det, primeFactors_twelve, Finset.prod_insert (by decide), Finset.prod_singleton, ite_eq_left rfl,
      ite_eq_right (by norm_num), pMassTwo_tau22, pMassOdd_sig22, stdP_two_five, stdP_three_five, stdMass_table_5]
    norm_num
  · intro p hp _ hdvd
    rw [g22_det] at hdvd
    have hp6 : p ∣ 2 * 3 := by exact_mod_cast hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hp6 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h; omega
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
      subst hp3
      exact ⟨isOddSymbolOf_g22, hsupp3⟩

/-! ### The automorphism counts -/

theorem posDefGram_a22 : PosDefGram a22 := posDefGram_a2Line 2 (by norm_num)

theorem posDefGram_a6 : PosDefGram a6 := by
  refine ⟨by ext i j; fin_cases i; fin_cases j; rfl, fun x hx => ?_⟩
  have e : x ⬝ᵥ (gramQ a6 *ᵥ x) = 6 * x 0 ^ 2 := by
    simp [gramQ, a6, dotProduct, mulVec]; ring
  rw [e]
  have h0 : x 0 ≠ 0 := fun h => hx (funext fun i => by fin_cases i; exact h)
  have := pow_pos (abs_pos.mpr h0) 2
  rw [sq_abs] at this
  linarith

set_option maxRecDepth 100000 in
/-- `|Aut(A₂ ⊥ ⟨2⟩)| = 24` (certified enumeration). -/
theorem card_aut_a22 : Nat.card (Aut (ofMatrixZ a22)) = 24 :=
  card_aut_eq_of_cert (posDef_ofMatrixZ_of_posDefGram _ posDefGram_a22) (C := !![4, 2, 0; 2, 4, 0; 0, 0, 3]) (D := 12) (B := 1) (by decide)
    (by norm_num) (by decide) autA2Line (by decide) (by decide) (by decide)

/-- `|Aut⟨6⟩| = 2` (certified enumeration). -/
theorem card_aut_a6 : Nat.card (Aut (ofMatrixZ a6)) = 2 :=
  card_aut_eq_of_cert (posDef_ofMatrixZ_of_posDefGram _ posDefGram_a6) (C := !![1]) (D := 12) (B := 1) (by decide)
    (by norm_num) (by decide) [!![-1], !![1]] (by decide) (by decide) (by decide)

/-- `A₂ ⊥ ⟨2⟩` has no vector of norm `1` (its norms are even). -/
theorem a22_ne_one (x : Fin 3 → ℤ) : x ⬝ᵥ (a22 *ᵥ x) ≠ 1 := by
  intro h
  have e : x ⬝ᵥ (a22 *ᵥ x) = 2 * (x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 + x 2 ^ 2) := by
    simp [a22, dotProduct, mulVec, Fin.sum_univ_three]; ring
  rw [e] at h
  generalize x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 + x 2 ^ 2 = t at h
  omega

/-- `⟨6⟩` has no vector of norm `1`. -/
theorem a6_ne_one (x : Fin 1 → ℤ) : x ⬝ᵥ (a6 *ᵥ x) ≠ 1 := by
  intro h
  have e : x ⬝ᵥ (a6 *ᵥ x) = 6 * x 0 ^ 2 := by simp [a6, dotProduct, mulVec]; ring
  rw [e] at h
  generalize x 0 ^ 2 = t at h
  omega

/-- `|Aut(K₂₂)| = |Aut(A₂ ⊥ ⟨2⟩ ⊥ I₂)| = 2²·2!·24 = 192`. -/
theorem card_aut_g22 : Nat.card (Aut (ofMatrixZ g22)) = 192 := by
  rw [g22, card_aut_sumI posDefGram_a22 a22_ne_one 2, card_aut_a22]; decide

/-- `|Aut(K₆)| = |Aut(⟨6⟩ ⊥ I₄)| = 2⁴·4!·2 = 768`. -/
theorem card_aut_k6 : Nat.card (Aut (ofMatrixZ k6)) = 768 := by
  rw [k6, card_aut_sumI posDefGram_a6 a6_ne_one 4, card_aut_a6]; decide

/-! ### `K₂₂` and `K₆` are in one genus -/

/-- From `K₆` to `K₂₂` at the prime 2: `A₂ᵀ K₂₂ A₂ = 4 K₆`. -/
def tA2 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-2, 0, 0, -1, -1; -4, 0, 0, 0, 0; 0, 0, 0, -1, 1; 0, -2, 0, 0, 0; 0, 0, -2, 0, 0]

/-- `4 A₂⁻¹`. -/
def tD2 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, -1, 0, 0, 0; 0, 0, 0, -2, 0; 0, 0, 0, 0, -2; -2, 1, -2, 0, 0; -2, 1, 2, 0, 0]

/-- From `K₆` to `K₂₂` at the prime 3: `A₃ᵀ K₂₂ A₃ = 9 K₆`. -/
def tA3 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 0, 2, -1, -1; 0, 0, 1, -2, 1; 3, 0, -1, -1, -1; 0, -3, 0, 0, 0; -6, 0, -1, -1, -1]

/-- `9 A₃⁻¹`. -/
def tD3 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 0, 1, 0, -1; 0, 0, 0, -3, 0; 3, 0, -2, 0, -1; 0, -3, -2, 0, -1; -3, 3, -2, 0, -1]

theorem tA2_spec : tA2ᵀ * g22 * tA2 = (2 ^ 2 : ℤ) • k6 := by rw [g22_eq, k6_eq]; decide
theorem tA3_spec : tA3ᵀ * g22 * tA3 = (3 ^ 2 : ℤ) • k6 := by rw [g22_eq, k6_eq]; decide
theorem tA2_tD2 : ∀ i j, (tA2 * tD2) i j = if i = j then (2 : ℤ) ^ 2 else 0 := by decide
theorem tD2_tA2 : ∀ i j, (tD2 * tA2) i j = if i = j then (2 : ℤ) ^ 2 else 0 := by decide
theorem tA3_tD3 : ∀ i j, (tA3 * tD3) i j = if i = j then (3 : ℤ) ^ 2 else 0 := by decide
theorem tD3_tA3 : ∀ i j, (tD3 * tA3) i j = if i = j then (3 : ℤ) ^ 2 else 0 := by decide

theorem eval_scaled {A : Matrix (Fin 5) (Fin 5) ℤ} {c : ℤ} (h : Aᵀ * g22 * A = (c ^ 2) • k6) (x : Fin 5 → ℤ) :
    (ofMatrixZ g22).eval (A *ᵥ x) = (c ^ 2 • ofMatrixZ k6).eval x := by
  rw [eval_smul_form, eval_ofMatrixZ, eval_ofMatrixZ, quad_mulVec, h, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

/-- An integer prime to `p` is a unit of `ℤ_p`. -/
theorem isUnit_int_padic (p : ℕ) [Fact p.Prime] (c : ℤ) (h : ¬ (p : ℤ) ∣ c) : IsUnit (c : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => h ?_)
  exact (PadicInt.norm_int_lt_one_iff_dvd _).mp hlt

/-- **`K₂₂` and `K₆` are in one genus.** -/
theorem sameGenus_g22_k6 : SameGenus (ofMatrixZ g22) (ofMatrixZ k6) := by
  refine ⟨fun p _ => ?_, ?_⟩
  · by_cases hp2 : p = 2
    · subst hp2
      have hu := isUnit_int_padic 2 3 (by decide)
      exact isometricGL_of_scaled (Int.castRingHom ℤ_[2]) 3 hu.unit (by simp)
        tA3_tD3 tD3_tA3 (eval_scaled tA3_spec)
    · have hu := isUnit_int_padic p 2 (fun h => hp2 (by
        have h2 : p ∣ 2 := by exact_mod_cast h
        exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2))
      exact isometricGL_of_scaled (Int.castRingHom ℤ_[p]) 2 hu.unit (by simp)
        tA2_tD2 tD2_tA2 (eval_scaled tA2_spec)
  · exact isometricGL_of_scaled (Int.castRingHom ℝ) 2 (Units.mk0 2 two_ne_zero) (by simp)
      tA2_tD2 tD2_tA2 (eval_scaled tA2_spec)

/-! ### `K₂₂` and `K₆` are not equivalent -/

/-- The vectors of norm `1` of `K₂₂` lie in its `I₂`. -/
theorem g22_norm_one {x : Fin 5 → ℤ} (h : (ofMatrixZ g22).eval x = 1) : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
  rw [eval_g22] at h
  have ht : 0 ≤ x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 := by
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0), sq_nonneg (x 1)]
  have h3 := sq_nonneg (x 3); have h4 := sq_nonneg (x 4); have h2 := sq_nonneg (x 2)
  have e : 2 * (x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2) + 2 * x 2 ^ 2 + (x 3 ^ 2 + x 4 ^ 2) = 1 := by linarith
  have ht0 : x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 = 0 := by omega
  have hs0 : x 2 ^ 2 = 0 := by omega
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (2 * x 0 - x 1), sq_nonneg (x 1)]
  rw [h1] at ht0
  refine ⟨by nlinarith, h1, pow_eq_zero_iff two_ne_zero |>.mp hs0⟩

/-- **`K₂₂ ≇ K₆`.** -/
theorem not_intEquiv_g22_k6 : ¬ IntEquiv (ofMatrixZ g22) (ofMatrixZ k6) := by
  rintro ⟨g, hg⟩
  have hu : ∀ i : Fin 5, i ≠ 0 → (g.val *ᵥ Pi.single i 1) 0 = 0 ∧ (g.val *ᵥ Pi.single i 1) 1 = 0 ∧
      (g.val *ᵥ Pi.single i 1) 2 = 0 := by
    intro i hi
    refine g22_norm_one ?_
    rw [hg, eval_k6]
    fin_cases i <;> simp_all
  set y : Fin 5 → ℤ := Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 with hy
  have hgy : g.val *ᵥ y = g.val *ᵥ Pi.single 1 1 + g.val *ᵥ Pi.single 2 1 + g.val *ᵥ Pi.single 3 1 := by
    rw [hy, Matrix.mulVec_add, Matrix.mulVec_add]
  have h1 := hu 1 (by decide); have h2 := hu 2 (by decide); have h3 := hu 3 (by decide)
  have hq := hg y
  rw [eval_k6, eval_g22, hgy] at hq
  simp only [Pi.add_apply, h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2, h3.1, h3.2.1, h3.2.2] at hq
  simp [hy] at hq
  have key : ∀ s t : ℤ, s ^ 2 + t ^ 2 ≠ 3 := by
    intro s t h
    rcases Int.even_or_odd s with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases Int.even_or_odd t with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
      ring_nf at h <;> omega
  exact key _ _ hq

/-! ### The genus has two classes -/

/-- The two classes of the genus. -/
def gen22 : Fin 2 → QuadForm ℤ 5 := ![ofMatrixZ g22, ofMatrixZ k6]

theorem gen22_sameGenus (i : Fin 2) : SameGenus (ofMatrixZ g22) (gen22 i) := by
  fin_cases i
  · exact SameGenus.refl _
  · exact sameGenus_g22_k6

theorem gen22_distinct (i j : Fin 2) (h : IntEquiv (gen22 i) (gen22 j)) : i = j := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h not_intEquiv_g22_k6
  · exact absurd (IsometricGL.symm h) not_intEquiv_g22_k6
  · rfl

theorem gen22_mass : ∑ i, ((Nat.card (Aut (gen22 i)) : ℝ))⁻¹ = Siegel.mass (ofMatrixZ g22) := by
  rw [Fin.sum_univ_two, mass_g22]
  simp only [gen22, Matrix.cons_val_zero, Matrix.cons_val_one, card_aut_g22, card_aut_k6]
  norm_num

/-- **The genus of `K₂₂` is `{K₂₂, K₆}`.** -/
theorem genusClasses_g22 : genusClasses (ofMatrixZ g22) = Set.range fun i => classOf (gen22 i) :=
  genusClasses_eq_of_sum_eq_mass posDef_g22 gen22 gen22_sameGenus gen22_distinct gen22_mass

/-- **Representation by the genus of `K₂₂`**: a positive definite form represented by `K₂₂` over
every `ℤ_p` is represented by `K₂₂` or by `K₆`. -/
theorem rep_g22_or_k6 {v : ℕ} {φ : QuadForm ℤ v} (hφ : IntQF.PosDef φ)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], Watson1963.RepOver ℤ_[p] (ofMatrixZ g22) φ) :
    Watson1963.Rep (ofMatrixZ g22) φ ∨ Watson1963.Rep (ofMatrixZ k6) φ := by
  obtain ⟨f', hg, hr⟩ := Watson1963.exists_sameGenus_rep posDef_g22 hφ hloc
  obtain ⟨i, hi⟩ := exists_intEquiv_of_sum_eq_mass posDef_g22 gen22 gen22_sameGenus gen22_distinct
    gen22_mass hg
  fin_cases i
  · exact Or.inl (Watson1963.Rep.of_intEquiv_left (IsometricGL.symm hi) hr)
  · exact Or.inr (Watson1963.Rep.of_intEquiv_left (IsometricGL.symm hi) hr)

end KimKimOh.Genera

import QuadFormsKB.Literature.ConwaySloane.Mass.Vines
import QuadFormsKB.Literature.ConwaySloane.Mass.Examples
import QuadFormsKB.Literature.ConwaySloane.Mass.StandardMass
import QuadFormsKB.Literature.ConwaySloane.OddClassification
import QuadFormsKB.Literature.ConwaySloane.TwoAdicForm
import QuadFormsKB.Siegel.KneserAut

/-!
# `K₃` and `K₉`: genus symbols, local masses, automorphism counts

`K₃ = A₂ ⊥ I₃` and `K₉ = A₂ ⊥ ⟨3⟩ ⊥ I₂`, with Gram matrices `g3 = sumI a2 3` and
`g9 = sumI a23 2` (`A₂` first). This file collects the finite inputs of the mass computation:

* the 2-adic symbols `1^{-5}_3` and `1^{+5}_5`, and the 3-adic symbols `1^{-4}3^{-1}` and
  `1^{-3}3^{-2}` (`IsTwoSymbolOf`, `IsOddSymbolOf`);
* the local masses `m₂ = 2/9, 2/15` and `m₃ = 729/320, 729/64` (Conway–Sloane (3)), and the
  standard factors `std₂ = 32/45`, `std₃ = 729/1280`;
* `|Aut(A₂ ⊥ I₃)| = 576` and `|Aut(A₂ ⊥ ⟨3⟩ ⊥ I₂)| = 192`, from the vine lemma
  `card_aut_sumI` and certified enumerations of `Aut(A₂)` (12) and `Aut(A₂ ⊥ ⟨3⟩)` (24).
-/

open Matrix

namespace KimKimOh.Genera

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass QuadFormsKB.Siegel.Kneser

/-! ### The Gram matrices -/

/-- `A₂`. -/
def a2 : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 2]

/-- `A₂ ⊥ ⟨3⟩`. -/
def a23 : Matrix (Fin 3) (Fin 3) ℤ := !![2, -1, 0; -1, 2, 0; 0, 0, 3]

/-- `K₃ = A₂ ⊥ I₃`. -/
def g3 : Matrix (Fin 5) (Fin 5) ℤ := sumI a2 3

/-- `K₉ = A₂ ⊥ ⟨3⟩ ⊥ I₂`. -/
def g9 : Matrix (Fin 5) (Fin 5) ℤ := sumI a23 2

theorem g3_eq : g3 = !![2, -1, 0, 0, 0; -1, 2, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem g9_eq : g9 = !![2, -1, 0, 0, 0; -1, 2, 0, 0, 0; 0, 0, 3, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem g3_symm : g3.IsSymm := by
  rw [g3_eq]; exact Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl

theorem g9_symm : g9.IsSymm := by
  rw [g9_eq]; exact Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl

theorem g3_det : g3.det = 3 := by
  rw [g3_eq]; simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem g9_det : g9.det = 9 := by
  rw [g9_eq]; simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem eval_g3 (x : Fin 5 → ℤ) : (ofMatrixZ g3).eval x =
    2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 := by
  rw [eval_ofMatrixZ, g3_eq]
  simp [dotProduct, mulVec, Fin.sum_univ_five]
  ring

theorem eval_g9 (x : Fin 5 → ℤ) : (ofMatrixZ g9).eval x =
    2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 + 3 * x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 := by
  rw [eval_ofMatrixZ, g9_eq]
  simp [dotProduct, mulVec, Fin.sum_univ_five]
  ring

theorem posDef_g3 : IntQF.PosDef (ofMatrixZ g3) := by
  intro x hx
  rw [eval_g3]
  by_contra h
  apply hx
  have key : x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 ≤ 0 := by
    have e : x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 =
        2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 := by ring
    rw [e]; exact not_lt.mp h
  have p0 := sq_nonneg (x 0); have p1 := sq_nonneg (x 1); have p01 := sq_nonneg (x 0 - x 1)
  have p2 := sq_nonneg (x 2); have p3 := sq_nonneg (x 3); have p4 := sq_nonneg (x 4)
  have z : ∀ t : ℤ, t ^ 2 ≤ 0 → t = 0 := fun t ht => pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm ht (sq_nonneg t))
  have h0 := z (x 0) (by linarith); have h1 := z (x 1) (by linarith); have h2 := z (x 2) (by linarith)
  have h3 := z (x 3) (by linarith); have h4 := z (x 4) (by linarith)
  funext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]

theorem posDef_g9 : IntQF.PosDef (ofMatrixZ g9) := by
  intro x hx
  rw [eval_g9]
  by_contra h
  apply hx
  have key : x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 + 3 * x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 ≤ 0 := by
    have e : x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 + 3 * x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 =
        2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 + 3 * x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 := by ring
    rw [e]; exact not_lt.mp h
  have p0 := sq_nonneg (x 0); have p1 := sq_nonneg (x 1); have p01 := sq_nonneg (x 0 - x 1)
  have p2 := sq_nonneg (x 2); have p3 := sq_nonneg (x 3); have p4 := sq_nonneg (x 4)
  have z : ∀ t : ℤ, t ^ 2 ≤ 0 → t = 0 := fun t ht => pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm ht (sq_nonneg t))
  have h0 := z (x 0) (by linarith); have h1 := z (x 1) (by linarith); have h2 := z (x 2) (by linarith)
  have h3 := z (x 3) (by linarith); have h4 := z (x 4) (by linarith)
  funext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]

/-! ### Equivalence over `ℤ_p` from an integral change of basis -/

/-- An integral `T` with `p ∤ det T` and `Tᵀ A T = B` gives `A ≅ B` over `ℤ_p`. -/
theorem zpEquiv_of_int (p : ℕ) [Fact p.Prime] {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    (T : Matrix (Fin n) (Fin n) ℤ) (hT : ¬ (p : ℤ) ∣ T.det) (h : Tᵀ * A * T = B) :
    Cassels.ZpEquiv (A.map (Int.cast : ℤ → ℚ_[p])) (B.map (Int.cast : ℤ → ℚ_[p])) := by
  set Tp : Matrix (Fin n) (Fin n) ℤ_[p] := T.map (Int.cast : ℤ → ℤ_[p]) with hTp
  have hdet : IsUnit Tp.det := by
    have e : Tp.det = ((T.det : ℤ) : ℤ_[p]) := (RingHom.map_det (Int.castRingHom ℤ_[p]) T).symm
    rw [e, PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hT ?_)
    exact (PadicInt.norm_int_lt_one_iff_dvd _).mp hlt
  refine ⟨Matrix.nonsingInvUnit Tp hdet, ?_⟩
  have hmap : (Matrix.nonsingInvUnit Tp hdet).val.map PadicInt.Coe.ringHom =
      T.map (Int.cast : ℤ → ℚ_[p]) := by
    ext i j
    simp [hTp, Matrix.nonsingInvUnit]
  have e : ∀ M N : Matrix (Fin n) (Fin n) ℤ,
      (M * N).map (Int.cast : ℤ → ℚ_[p]) = M.map Int.cast * N.map Int.cast :=
    fun M N => Matrix.map_mul (f := Int.castRingHom ℚ_[p])
  rw [hmap, ← h, e, e, Matrix.transpose_map]

/-! ### `2` in `ℚ₃` -/

theorem norm_two_padic_three : ‖(2 : ℚ_[3])‖ = 1 := by
  have h1 := Padic.norm_int_le_one (p := 3) 2
  have h2 : ¬ ‖((2 : ℤ) : ℚ_[3])‖ < 1 := by
    rw [Padic.norm_intCast_lt_one_iff]; norm_num
  have : ‖((2 : ℤ) : ℚ_[3])‖ = 1 := le_antisymm h1 (not_lt.mp h2)
  simpa using this

/-- `2` is not a square in `ℚ₃` (as in Hanke's `not_isSquare_two_padic_three`). -/
theorem not_isSquare_two_padic_three : ¬ IsSquare (2 : ℚ_[3]) := by
  rintro ⟨y, hy⟩
  have hn : ‖y‖ = 1 := by
    have h := congrArg norm hy
    rw [norm_two_padic_three, norm_mul] at h
    nlinarith [norm_nonneg y]
  let z : ℤ_[3] := ⟨y, (PadicInt.mem_subring_iff 3).2 hn.le⟩
  have hz : z * z = 2 := Subtype.ext (by show y * y = 2; exact hy.symm)
  have h := congrArg PadicInt.toZMod hz
  rw [map_mul, map_ofNat] at h
  revert h
  generalize PadicInt.toZMod z = w
  revert w
  decide

/-! ### The 2-adic symbols -/

/-- `1^{-5}_3`, the 2-adic symbol of `A₂ ⊥ I₃`. -/
def tau3 : TwoSymbol := fun k => if k = 0 then ⟨5, .minus, .I, 3⟩ else TwoFactor.trivial

/-- `1^{+5}_5`, the 2-adic symbol of `A₂ ⊥ ⟨3⟩ ⊥ I₂`. -/
def tau9 : TwoSymbol := fun k => if k = 0 then ⟨5, .plus, .I, 5⟩ else TwoFactor.trivial

/-- The block decomposition `(2x²+2xy+2y²) ⊥ ⟨1⟩ ⊥ ⟨1⟩ ⊥ ⟨1⟩` of `A₂ ⊥ I₃` over `ℤ₂`. -/
def blocks3 : List Cassels.DyBlock := [.ell 0, .sq 0 1, .sq 0 1, .sq 0 1]

/-- The block decomposition `(2x²+2xy+2y²) ⊥ ⟨3⟩ ⊥ ⟨1⟩ ⊥ ⟨1⟩` of `A₂ ⊥ ⟨3⟩ ⊥ I₂` over `ℤ₂`. -/
def blocks9 : List Cassels.DyBlock := [.ell 0, .sq 0 3, .sq 0 1, .sq 0 1]

/-- The block matrix of `blocks3`. -/
def gb3 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, 1, 0, 0, 0; 1, 2, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

/-- The block matrix of `blocks9`. -/
def gb9 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, 1, 0, 0, 0; 1, 2, 0, 0, 0; 0, 0, 3, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

/-- The sign change `y ↦ -y` in the `A₂` coordinates. -/
def flip : Matrix (Fin 5) (Fin 5) ℤ := Matrix.diagonal ![1, -1, 1, 1, 1]

theorem flip_det : ¬ (2 : ℤ) ∣ flip.det := by
  rw [flip, Matrix.det_diagonal, Fin.prod_univ_five]; decide

theorem flip_g3 : flipᵀ * g3 * flip = gb3 := by rw [g3_eq]; decide

theorem flip_g9 : flipᵀ * g9 * flip = gb9 := by rw [g9_eq]; decide

theorem map_orthSumMat {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℤ) (S : Matrix (Fin b) (Fin b) ℤ) :
    (Cassels.orthSumMat A S).map (Int.cast : ℤ → ℚ_[2]) =
      Cassels.orthSumMat (A.map Int.cast) (S.map Int.cast) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [Cassels.orthSumMat]

theorem mat_ell0 : (Cassels.DyBlock.ell 0).mat = (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).map Int.cast := by
  show ((2 : ℚ_[2]) ^ (0 : ℤ) • !![(2 : ℚ_[2]), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) =
    (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).map Int.cast
  rw [zpow_zero, one_smul]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem mat_sq0 (u : ℤ) : (Cassels.DyBlock.sq 0 u).mat = (!![u] : Matrix (Fin 1) (Fin 1) ℤ).map Int.cast := by
  show (!![(2 : ℚ_[2]) ^ (0 : ℤ) * (u : ℚ_[2])] : Matrix (Fin 1) (Fin 1) ℚ_[2]) =
    (!![u] : Matrix (Fin 1) (Fin 1) ℤ).map Int.cast
  ext i j; fin_cases i; fin_cases j; simp

theorem map_zero_fin0 : (0 : Matrix (Fin 0) (Fin 0) ℤ).map (Int.cast : ℤ → ℚ_[2]) = 0 := by
  ext i; exact i.elim0

/-- `blocks3` as an integral block matrix. -/
def ib3 : Matrix (Fin 5) (Fin 5) ℤ := Cassels.orthSumMat !![2, 1; 1, 2]
  (Cassels.orthSumMat !![1] (Cassels.orthSumMat !![1] (Cassels.orthSumMat !![1] (0 : Matrix (Fin 0) (Fin 0) ℤ))))

/-- `blocks9` as an integral block matrix. -/
def ib9 : Matrix (Fin 5) (Fin 5) ℤ := Cassels.orthSumMat !![2, 1; 1, 2]
  (Cassels.orthSumMat !![3] (Cassels.orthSumMat !![1] (Cassels.orthSumMat !![1] (0 : Matrix (Fin 0) (Fin 0) ℤ))))

theorem ib3_eq : ib3 = gb3 := by decide

theorem ib9_eq : ib9 = gb9 := by decide

theorem dyMat_blocks3_eq : Cassels.dyMat blocks3 = ib3.map Int.cast := by
  show Cassels.orthSumMat _ (Cassels.orthSumMat _ (Cassels.orthSumMat _ (Cassels.orthSumMat _ 0))) = _
  rw [ib3, map_orthSumMat, map_orthSumMat, map_orthSumMat, map_orthSumMat, map_zero_fin0, mat_ell0, mat_sq0]
  rfl

theorem dyMat_blocks9_eq : Cassels.dyMat blocks9 = ib9.map Int.cast := by
  show Cassels.orthSumMat _ (Cassels.orthSumMat _ (Cassels.orthSumMat _ (Cassels.orthSumMat _ 0))) = _
  rw [ib9, map_orthSumMat, map_orthSumMat, map_orthSumMat, map_orthSumMat, map_zero_fin0, mat_ell0, mat_sq0,
    mat_sq0]
  rfl

theorem dyMat_blocks3 :
    (Cassels.dyMat blocks3).submatrix (Fin.cast rfl) (Fin.cast rfl) = gb3.map (Int.cast : ℤ → ℚ_[2]) := by
  rw [dyMat_blocks3_eq, ib3_eq]; rfl

theorem dyMat_blocks9 :
    (Cassels.dyMat blocks9).submatrix (Fin.cast rfl) (Fin.cast rfl) = gb9.map (Int.cast : ℤ → ℚ_[2]) := by
  rw [dyMat_blocks9_eq, ib9_eq]; rfl

theorem isTwoSymbolOf_g3 : IsTwoSymbolOf (g3.map (Int.cast : ℤ → ℚ_[2])) tau3 := by
  refine ⟨blocks3, ?_, ?_, rfl, ?_, ?_⟩
  · intro b hb
    simp only [blocks3, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [Cassels.DyBlock.Valid]
  · intro b hb
    simp only [blocks3, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [blockExp]
  · have h := zpEquiv_of_int 2 flip flip_det flip_g3
    rw [← dyMat_blocks3] at h
    exact h
  · funext k
    by_cases hk : k = 0
    · subst hk
      simp only [tau3, ite_true, blockSymbol, blocks3]
      decide
    · have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk
      have hf : List.filter (fun b => decide (blockExp b = (k : ℤ))) blocks3 = [] := by
        simp [blocks3, blockExp, hk'.symm]
      show (if k = 0 then _ else TwoFactor.trivial) = blockSymbol blocks3 k
      rw [ite_eq_right hk]
      unfold blockSymbol
      simp only [hf]
      rfl

theorem isTwoSymbolOf_g9 : IsTwoSymbolOf (g9.map (Int.cast : ℤ → ℚ_[2])) tau9 := by
  refine ⟨blocks9, ?_, ?_, rfl, ?_, ?_⟩
  · intro b hb
    simp only [blocks9, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [Cassels.DyBlock.Valid]
  · intro b hb
    simp only [blocks9, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [blockExp]
  · have h := zpEquiv_of_int 2 flip flip_det flip_g9
    rw [← dyMat_blocks9] at h
    exact h
  · funext k
    by_cases hk : k = 0
    · subst hk
      simp only [tau9, ite_true, blockSymbol, blocks9]
      decide
    · have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk
      have hf : List.filter (fun b => decide (blockExp b = (k : ℤ))) blocks9 = [] := by
        simp [blocks9, blockExp, hk'.symm]
      show (if k = 0 then _ else TwoFactor.trivial) = blockSymbol blocks9 k
      rw [ite_eq_right hk]
      unfold blockSymbol
      simp only [hf]
      rfl

/-! ### The 3-adic symbols -/

/-- `1^{-4}3^{-1}`, the 3-adic symbol of `A₂ ⊥ I₃`. -/
def sig3 : OddSymbol := fun k => if k = 0 then ⟨4, .minus⟩ else if k = 1 then ⟨1, .minus⟩ else OddFactor.trivial

/-- `1^{-3}3^{-2}`, the 3-adic symbol of `A₂ ⊥ ⟨3⟩ ⊥ I₂`. -/
def sig9 : OddSymbol := fun k => if k = 0 then ⟨3, .minus⟩ else if k = 1 then ⟨2, .minus⟩ else OddFactor.trivial

/-- The change of basis `(e₀, e₀ + 2e₁, e₂, e₃, e₄)`, of determinant `2`, diagonalizing `A₂` over `ℤ₃`. -/
def T3 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 1, 0, 0, 0; 0, 2, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem T3_det : ¬ (3 : ℤ) ∣ T3.det := by
  rw [T3]; simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem T3_g3 : T3ᵀ * g3 * T3 = Matrix.diagonal ![2, 6, 1, 1, 1] := by rw [g3_eq]; decide

theorem T3_g9 : T3ᵀ * g9 * T3 = Matrix.diagonal ![2, 6, 3, 1, 1] := by rw [g9_eq]; decide

/-- The unit parts. -/
noncomputable def u3 : Fin 5 → ℚ_[3] := ![2, 2, 1, 1, 1]

theorem norm_u3 (i : Fin 5) : ‖u3 i‖ = 1 := by
  fin_cases i <;> simp [u3, norm_two_padic_three]

theorem isOddSymbolOf_g3 : IsOddSymbolOf 3 (g3.map (Int.cast : ℤ → ℚ_[3])) sig3 := by
  refine ⟨![0, 1, 0, 0, 0], u3, norm_u3, ?_, ?_⟩
  · have e : (Matrix.diagonal fun i => ((3 : ℕ) : ℚ_[3]) ^ ((![0, 1, 0, 0, 0] : Fin 5 → ℕ) i) * u3 i) =
        (Matrix.diagonal ![2, 6, 1, 1, 1] : Matrix (Fin 5) (Fin 5) ℤ).map (Int.cast : ℤ → ℚ_[3]) := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [u3, Matrix.diagonal]
    rw [e]
    exact zpEquiv_of_int 3 T3 T3_det T3_g3
  · funext k
    rcases k with _ | _ | k
    · have hp : (∏ i : {i : Fin 5 // (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i = 0}, u3 i) = 2 := by
        rw [← Finset.prod_subtype ({0, 2, 3, 4} : Finset (Fin 5)) (by decide) u3]
        simp [u3, Finset.prod_insert]
      simp only [sig3, oddSymbolOfDiag, ite_true, hp, not_isSquare_two_padic_three, ite_false,
        OddFactor.mk.injEq, and_true]
      rw [Fintype.card_subtype]; decide
    · have hp : (∏ i : {i : Fin 5 // (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i = 0 + 1}, u3 i) = 2 := by
        rw [← Finset.prod_subtype ({1} : Finset (Fin 5)) (by decide) u3]
        simp [u3]
      simp only [sig3, oddSymbolOfDiag, show (0 + 1 : ℕ) ≠ 0 by omega, ite_false, ite_true, hp,
        not_isSquare_two_padic_three, OddFactor.mk.injEq, and_true]
      rw [Fintype.card_subtype]; decide
    · have he : ∀ i : Fin 5, (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i ≠ k + 1 + 1 := by
        intro i; fin_cases i <;> simp
      have : IsEmpty {i : Fin 5 // (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i = k + 1 + 1} := ⟨fun ⟨i, hi⟩ => he i hi⟩
      have hsq : IsSquare (∏ i : {i : Fin 5 // (![0, 1, 0, 0, 0] : Fin 5 → ℕ) i = k + 1 + 1}, u3 i) := by
        rw [Finset.univ_eq_empty, Finset.prod_empty]; exact ⟨1, (mul_one 1).symm⟩
      simp only [sig3, oddSymbolOfDiag, show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ite_false,
        OddFactor.trivial, hsq, ite_true, OddFactor.mk.injEq, and_true]
      symm
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => he i hi⟩

theorem isOddSymbolOf_g9 : IsOddSymbolOf 3 (g9.map (Int.cast : ℤ → ℚ_[3])) sig9 := by
  refine ⟨![0, 1, 1, 0, 0], u3, norm_u3, ?_, ?_⟩
  · have e : (Matrix.diagonal fun i => ((3 : ℕ) : ℚ_[3]) ^ ((![0, 1, 1, 0, 0] : Fin 5 → ℕ) i) * u3 i) =
        (Matrix.diagonal ![2, 6, 3, 1, 1] : Matrix (Fin 5) (Fin 5) ℤ).map (Int.cast : ℤ → ℚ_[3]) := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [u3, Matrix.diagonal]
    rw [e]
    exact zpEquiv_of_int 3 T3 T3_det T3_g9
  · funext k
    rcases k with _ | _ | k
    · have hp : (∏ i : {i : Fin 5 // (![0, 1, 1, 0, 0] : Fin 5 → ℕ) i = 0}, u3 i) = 2 := by
        rw [← Finset.prod_subtype ({0, 3, 4} : Finset (Fin 5)) (by decide) u3]
        simp [u3, Finset.prod_insert]
      simp only [sig9, oddSymbolOfDiag, ite_true, hp, not_isSquare_two_padic_three, ite_false,
        OddFactor.mk.injEq, and_true]
      rw [Fintype.card_subtype]; decide
    · have hp : (∏ i : {i : Fin 5 // (![0, 1, 1, 0, 0] : Fin 5 → ℕ) i = 0 + 1}, u3 i) = 2 := by
        rw [← Finset.prod_subtype ({1, 2} : Finset (Fin 5)) (by decide) u3]
        simp [u3, Finset.prod_insert]
      simp only [sig9, oddSymbolOfDiag, show (0 + 1 : ℕ) ≠ 0 by omega, ite_false, ite_true, hp,
        not_isSquare_two_padic_three, OddFactor.mk.injEq, and_true]
      rw [Fintype.card_subtype]; decide
    · have he : ∀ i : Fin 5, (![0, 1, 1, 0, 0] : Fin 5 → ℕ) i ≠ k + 1 + 1 := by
        intro i; fin_cases i <;> simp
      have : IsEmpty {i : Fin 5 // (![0, 1, 1, 0, 0] : Fin 5 → ℕ) i = k + 1 + 1} := ⟨fun ⟨i, hi⟩ => he i hi⟩
      have hsq : IsSquare (∏ i : {i : Fin 5 // (![0, 1, 1, 0, 0] : Fin 5 → ℕ) i = k + 1 + 1}, u3 i) := by
        rw [Finset.univ_eq_empty, Finset.prod_empty]; exact ⟨1, (mul_one 1).symm⟩
      simp only [sig9, oddSymbolOfDiag, show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ite_false,
        OddFactor.trivial, hsq, ite_true, OddFactor.mk.injEq, and_true]
      symm
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => he i hi⟩

/-! ### The local masses -/

theorem pMassTwo_tau3 : pMassTwo tau3 1 = 2 / 9 := by
  have hd : diagProdTwo tau3 1 = 2 / 9 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, tau3, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (tau3 k).dim) 1 = 0 := by decide
  have hII : nII tau3 1 = 0 := by decide
  have hII' : nII' tau3 1 = 0 := by decide
  rw [pMassTwo, hd, hc, hII, hII']; norm_num

theorem pMassTwo_tau9 : pMassTwo tau9 1 = 2 / 15 := by
  have hd : diagProdTwo tau9 1 = 2 / 15 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, tau9, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (tau9 k).dim) 1 = 0 := by decide
  have hII : nII tau9 1 = 0 := by decide
  have hII' : nII' tau9 1 = 0 := by decide
  rw [pMassTwo, hd, hc, hII, hII']; norm_num

theorem stdP_two_five (d : ℤ) : (stdP 2 5 d : ℝ) = 32 / 45 := by
  have h : stdP 2 5 d = 32 / 45 := by simp [stdP, lowerProd, Finset.prod_range_succ]; norm_num
  rw [h]; norm_num

theorem stdP_three_five (d : ℤ) : (stdP 3 5 d : ℝ) = 729 / 1280 := by
  have h : stdP 3 5 d = 729 / 1280 := by simp [stdP, lowerProd, Finset.prod_range_succ]; norm_num
  rw [h]; norm_num

theorem pMassOdd_sig3 : pMassOdd 3 sig3 2 = 729 / 320 := by
  have hd : (∏ k ∈ Finset.range 2, (oddSpecies 3 (sig3 k)).diagFactor 3) = 81 / 320 := by
    simp [sig3, Finset.prod_range_succ, oddSpecies, Species.diagFactor, lowerProd, Sign.flip, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (sig3 k).dim) 2 = 4 := by decide
  have h3 : Real.sqrt 3 ^ 4 = 9 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  rw [pMassOdd, hd, hc]; push_cast; rw [h3]; norm_num

theorem pMassOdd_sig9 : pMassOdd 3 sig9 2 = 729 / 64 := by
  have hd : (∏ k ∈ Finset.range 2, (oddSpecies 3 (sig9 k)).diagFactor 3) = 27 / 64 := by
    simp [sig9, Finset.prod_range_succ, oddSpecies, Species.diagFactor, lowerProd, Sign.flip, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (sig9 k).dim) 2 = 6 := by decide
  have h3 : Real.sqrt 3 ^ 6 = 27 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  rw [pMassOdd, hd, hc]; push_cast; rw [h3]; norm_num

/-! ### The automorphism counts -/

/-- `IntQF.PosDef` of `ofMatrixZ A` from `PosDefGram A`. -/
theorem posDef_ofMatrixZ_of_posDefGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h : PosDefGram A) :
    IntQF.PosDef (ofMatrixZ A) := by
  intro x hx
  rw [eval_ofMatrixZ]
  have h1 := h.2 (fun i => (x i : ℚ)) (fun h0 => hx (funext fun i => by
    have := congrFun h0 i
    simp only [Pi.zero_apply, Int.cast_eq_zero] at this
    exact this))
  have e : (fun i => (x i : ℚ)) ⬝ᵥ (gramQ A *ᵥ fun i => (x i : ℚ)) = ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) := by
    simp [gramQ, dotProduct, mulVec, Matrix.map_apply]
  rw [e] at h1
  exact_mod_cast h1

theorem posDefGram_a2 : PosDefGram a2 := by
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> rfl, fun x hx => ?_⟩
  have e : x ⬝ᵥ (gramQ a2 *ᵥ x) = x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 := by
    simp [gramQ, a2, dotProduct, mulVec, Fin.sum_univ_two]; ring
  rw [e]
  by_contra h
  apply hx
  have p0 := sq_nonneg (x 0); have p1 := sq_nonneg (x 1); have p01 := sq_nonneg (x 0 - x 1)
  have z : ∀ t : ℚ, t ^ 2 ≤ 0 → t = 0 := fun t ht => pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm ht (sq_nonneg t))
  have h0 := z (x 0) (by linarith); have h1 := z (x 1) (by linarith)
  funext i; fin_cases i <;> simp [h0, h1]

/-- **`A₂ ⊥ ⟨d⟩` is positive definite for `d > 0`**: its norm is
`x₀² + x₁² + (x₀ - x₁)² + d x₂²`. -/
theorem posDefGram_a2Line (d : ℤ) (hd : 0 < d) :
    PosDefGram (!![2, -1, 0; -1, 2, 0; 0, 0, d] : Matrix (Fin 3) (Fin 3) ℤ) := by
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> rfl, fun x hx => ?_⟩
  have e : x ⬝ᵥ (gramQ (!![2, -1, 0; -1, 2, 0; 0, 0, d] : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ x) =
      x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 + d * x 2 ^ 2 := by
    simp [gramQ, dotProduct, mulVec, Fin.sum_univ_three]; ring
  rw [e]
  by_contra h
  apply hx
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have p0 := sq_nonneg (x 0); have p1 := sq_nonneg (x 1); have p01 := sq_nonneg (x 0 - x 1)
  have p2 := mul_nonneg hd'.le (sq_nonneg (x 2))
  have z : ∀ t : ℚ, t ^ 2 ≤ 0 → t = 0 := fun t ht => pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm ht (sq_nonneg t))
  have h0 := z (x 0) (by linarith); have h1 := z (x 1) (by linarith)
  have h2 := z (x 2) (by nlinarith)
  funext i; fin_cases i <;> simp [h0, h1, h2]

theorem posDefGram_a23 : PosDefGram a23 := posDefGram_a2Line 3 (by norm_num)

/-- The 24 automorphisms of `A₂ ⊥ ⟨d⟩` for `d = 2, 3`: those of `A₂` with `±1` on the line. Each
use checks soundness and completeness for its own Gram matrix. -/
def autA2Line : List (Matrix (Fin 3) (Fin 3) ℤ) :=
  [!![-1, 0, 0; -1, 1, 0; 0, 0, -1], !![-1, 0, 0; -1, 1, 0; 0, 0, 1], !![-1, 1, 0; -1, 0, 0; 0, 0, -1],
    !![-1, 1, 0; -1, 0, 0; 0, 0, 1], !![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1],
    !![-1, 1, 0; 0, 1, 0; 0, 0, -1], !![-1, 1, 0; 0, 1, 0; 0, 0, 1], !![0, -1, 0; -1, 0, 0; 0, 0, -1],
    !![0, -1, 0; -1, 0, 0; 0, 0, 1], !![0, 1, 0; -1, 1, 0; 0, 0, -1], !![0, 1, 0; -1, 1, 0; 0, 0, 1],
    !![0, -1, 0; 1, -1, 0; 0, 0, -1], !![0, -1, 0; 1, -1, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, -1],
    !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, -1, 0; 0, -1, 0; 0, 0, -1], !![1, -1, 0; 0, -1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 1, 0; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, -1, 0; 1, 0, 0; 0, 0, -1],
    !![1, -1, 0; 1, 0, 0; 0, 0, 1], !![1, 0, 0; 1, -1, 0; 0, 0, -1], !![1, 0, 0; 1, -1, 0; 0, 0, 1]]

/-- `|Aut(A₂)| = 12` (certified enumeration). -/
theorem card_aut_a2 : Nat.card (Aut (ofMatrixZ a2)) = 12 :=
  card_aut_eq_of_cert (posDef_ofMatrixZ_of_posDefGram _ posDefGram_a2) (C := !![4, 2; 2, 4]) (D := 12) (B := 1) (by decide) (by norm_num)
    (by decide) [!![-1, 0; -1, 1], !![-1, 1; -1, 0], !![-1, 0; 0, -1], !![-1, 1; 0, 1], !![0, -1; -1, 0], !![0, 1; -1, 1], !![0, -1; 1, -1], !![0, 1; 1, 0], !![1, -1; 0, -1], !![1, 0; 0, 1], !![1, -1; 1, 0], !![1, 0; 1, -1]] (by decide) (by decide) (by decide)

/-- `|Aut(A₂ ⊥ ⟨3⟩)| = 24` (certified enumeration). -/
theorem card_aut_a23 : Nat.card (Aut (ofMatrixZ a23)) = 24 :=
  card_aut_eq_of_cert (posDef_ofMatrixZ_of_posDefGram _ posDefGram_a23) (C := !![24, 12, 0; 12, 24, 0; 0, 0, 12]) (D := 72) (B := 1) (by decide)
    (by norm_num) (by decide) autA2Line (by decide) (by decide) (by decide)

/-- `A₂` has no vector of norm `1` (its norms are even). -/
theorem a2_ne_one (x : Fin 2 → ℤ) : x ⬝ᵥ (a2 *ᵥ x) ≠ 1 := by
  intro h
  have e : x ⬝ᵥ (a2 *ᵥ x) = 2 * (x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2) := by
    simp [a2, dotProduct, mulVec, Fin.sum_univ_two]; ring
  rw [e] at h
  generalize x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 = t at h
  omega

/-- `A₂ ⊥ ⟨3⟩` has no vector of norm `1`. -/
theorem a23_ne_one (x : Fin 3 → ℤ) : x ⬝ᵥ (a23 *ᵥ x) ≠ 1 := by
  intro h
  have e : x ⬝ᵥ (a23 *ᵥ x) = 2 * (x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2) + 3 * x 2 ^ 2 := by
    simp [a23, dotProduct, mulVec, Fin.sum_univ_three]; ring
  have ht : 0 ≤ x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 := by
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0), sq_nonneg (x 1)]
  have hs : 0 ≤ x 2 ^ 2 := sq_nonneg _
  rw [e] at h
  generalize x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 = t at h ht
  generalize x 2 ^ 2 = s at h hs
  omega

/-- `|Aut(K₃)| = |Aut(A₂ ⊥ I₃)| = 2³·3!·12 = 576`. -/
theorem card_aut_g3 : Nat.card (Aut (ofMatrixZ g3)) = 576 := by
  rw [g3, card_aut_sumI posDefGram_a2 a2_ne_one 3, card_aut_a2]; decide

/-- `|Aut(K₉)| = |Aut(A₂ ⊥ ⟨3⟩ ⊥ I₂)| = 2²·2!·24 = 192`. -/
theorem card_aut_g9 : Nat.card (Aut (ofMatrixZ g9)) = 192 := by
  rw [g9, card_aut_sumI posDefGram_a23 a23_ne_one 2, card_aut_a23]; decide

end KimKimOh.Genera

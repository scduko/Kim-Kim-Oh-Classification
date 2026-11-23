import KimKimOh.Local.BinaryData
import KimKimOh.Local.Diagonal
import KimKimOh.Local.LargePrimes

/-!
# Binary sources: `K₉` is locally 2-universal

`locallyRepresents_K9_binary`: `K₉ = I₂ ⊥ A₂ ⊥ ⟨3⟩` represents every binary integral form of
positive determinant over every `ℤ_p`.

* `p ≥ 5`: a binary `C` lies in the ternary `C ⊥ ⟨9⟩`, whose diagonal entry `9 · 1²` is in the
  square class of `det K₉ = 9` (`square_K9`).
* `p = 3`: every residue class of `C` modulo 9 has a witness for the diagonal sublattice `J93`
  (`w93`, checked by the kernel), and `lem:local-precision` applies.
* `p = 2`: 242 of the 256 residue classes modulo `(8, 4, 8)` have a witness for `J92` (`w92`).
  In the other 14, `C` has an integral superlattice of index 2: `C = Dᵀ C' D` with
  `det C' = det C / 4`. Induction on the determinant.
-/

namespace KimKimOh.LocalBinary

open Matrix Local

/-- The `5 × 2` matrix with the entries of a list, row-major. -/
def mat52 (l : List ℤ) : Matrix (Fin 5) (Fin 2) ℤ := Matrix.of fun i j => l.getD (2 * i.val + j.val) 0

/-- The binary Gram matrix `[[a, b], [b, c]]`. -/
def bin (a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, b; b, c]

/-! ### `p = 3` -/

/-- The test of a witness at 3: `Xᵀ J₉₃ X ≡ [[a, b], [b, c]] (mod 9)` and `Xᵀ Y ≡ 1 (mod 3)`. -/
def chk3 (a b c : ℤ) (w : List ℤ × List ℤ) : Bool :=
  decide (∀ i j, (bin a b c - (mat52 w.1)ᵀ * J93 * mat52 w.1) i j % 9 = 0) &&
    decide (∀ i j, ((mat52 w.1)ᵀ * mat52 w.2 - (1 : Matrix (Fin 2) (Fin 2) ℤ)) i j % 3 = 0)

theorem w93_ok : ∀ a : ℕ, a < 9 → ∀ b : ℕ, b < 9 → ∀ c : ℕ, c < 9 →
    chk3 a b c (w93.getD (81 * a + 9 * b + c) ([], [])) = true := by
  decide +kernel

/-- The residue of `x` modulo `m > 0`, as a natural number. -/
theorem exists_natCast_eq_emod (x m : ℤ) (hm : 0 < m) : ∃ a : ℕ, (a : ℤ) = x % m ∧ (a : ℤ) < m :=
  ⟨(x % m).toNat, Int.toNat_of_nonneg (Int.emod_nonneg x hm.ne'),
    by rw [Int.toNat_of_nonneg (Int.emod_nonneg x hm.ne')]; exact Int.emod_lt_of_pos x hm⟩

/-- **`K₉` represents every binary form over `ℤ₃`.** -/
theorem binary_three (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : Cᵀ = C) : LocallyRepresents K9.gram C 3 := by
  have hs : C 1 0 = C 0 1 := by simpa using congrFun (congrFun hC 0) 1
  obtain ⟨a, ha, ha9⟩ := exists_natCast_eq_emod (C 0 0) 9 (by norm_num)
  obtain ⟨b, hb, hb9⟩ := exists_natCast_eq_emod (C 0 1) 9 (by norm_num)
  obtain ⟨c, hc, hc9⟩ := exists_natCast_eq_emod (C 1 1) 9 (by norm_num)
  have hk := w93_ok a (by omega) b (by omega) c (by omega)
  set w := w93.getD (81 * a + 9 * b + c) ([], [])
  simp only [chk3, Bool.and_eq_true, decide_eq_true_eq] at hk
  rw [ha, hb, hc] at hk
  obtain ⟨h9', hY'⟩ := hk
  have h9 : ∀ i j, (9 : ℤ) ∣ (bin (C 0 0 % 9) (C 0 1 % 9) (C 1 1 % 9) - (mat52 w.1)ᵀ * J93 * mat52 w.1) i j :=
    fun i j => Int.dvd_of_emod_eq_zero (h9' i j)
  have hY : ∀ i j, (3 : ℤ) ∣ ((mat52 w.1)ᵀ * mat52 w.2 - (1 : Matrix (Fin 2) (Fin 2) ℤ)) i j :=
    fun i j => Int.dvd_of_emod_eq_zero (hY' i j)
  refine locallyRepresents_K9_three (mat52 w.1) (mat52 w.2) hY C hC fun i j => ?_
  have hCb : (9 : ℤ) ∣ (C - bin (C 0 0 % 9) (C 0 1 % 9) (C 1 1 % 9)) i j := by
    fin_cases i <;> fin_cases j <;> simp [bin, hs] <;> omega
  have := dvd_add hCb (h9 i j)
  simpa only [Matrix.sub_apply, sub_add_sub_cancel] using this

/-! ### `p = 2`, for any host with a table of witnesses -/

/-- The test at 2 for a host with Gram matrix `J` on `ℤ⁵` (and `Kc` the form pairing the witness
with its dual basis): a witness (tag 0), or the direction of a superlattice of index 2 (tags 1, 2,
3: `(1, 0)`, `(0, 1)`, `(1, 1)`). -/
def binChk2 (J Kc : Matrix (Fin 5) (Fin 5) ℤ) (a b c : ℤ) (e : ℕ × List ℤ × List ℤ) : Bool :=
  match e.1 with
  | 0 =>
    decide (∀ i j, (((mat52 e.2.1)ᵀ * J * mat52 e.2.1) i j - bin a b c i j) % 4 = 0) &&
      decide (∀ i, (((mat52 e.2.1)ᵀ * J * mat52 e.2.1) i i - bin a b c i i) % 8 = 0) &&
      decide (∀ i j, (((mat52 e.2.1)ᵀ * Kc * mat52 e.2.2) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j) % 2 = 0)
  | 1 => decide (a % 4 = 0 ∧ b % 2 = 0)
  | 2 => decide (c % 4 = 0 ∧ b % 2 = 0)
  | _ => decide ((a + b) % 2 = 0 ∧ (b + c) % 2 = 0 ∧ (a + 2 * b + c) % 4 = 0)

/-- **A host represents every binary form of positive determinant over `ℤ₂`** if a table gives,
for each residue class of `(a, b, c)` modulo `(8, 4, 8)`, a witness or a superlattice of index 2,
and witnesses lift (`hlift`, a Hensel step). -/
theorem binary_two_of_witnesses {ι : Type*} [Fintype ι] (K : Matrix ι ι ℤ) (J Kc : Matrix (Fin 5) (Fin 5) ℤ)
    (tab : List (ℕ × List ℤ × List ℤ))
    (htab : ∀ a : ℕ, a < 8 → ∀ b : ℕ, b < 4 → ∀ c : ℕ, c < 8 →
      binChk2 J Kc a b c (tab.getD (32 * a + 8 * b + c) (0, [], [])) = true)
    (hlift : ∀ X Y : Matrix (Fin 5) (Fin 2) ℤ,
      (∀ i j, (2 : ℤ) ∣ (Xᵀ * Kc * Y) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j) →
      ∀ C : Matrix (Fin 2) (Fin 2) ℤ, Cᵀ = C →
      (∀ i j, (4 : ℤ) ∣ (Xᵀ * J * X) i j - C i j) → (∀ i, (8 : ℤ) ∣ (Xᵀ * J * X) i i - C i i) →
      LocallyRepresents K C 2) :
    ∀ (n : ℕ) (C : Matrix (Fin 2) (Fin 2) ℤ), Cᵀ = C → C.det.toNat = n → 0 < C.det →
      LocallyRepresents K C 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C hC hn hdet
  have hs : C 1 0 = C 0 1 := by simpa using congrFun (congrFun hC 0) 1
  have hdetC : C.det = C 0 0 * C 1 1 - C 0 1 * C 0 1 := by rw [det_fin_two, hs]
  obtain ⟨a, ha, ha8⟩ := exists_natCast_eq_emod (C 0 0) 8 (by norm_num)
  obtain ⟨b, hb, hb4⟩ := exists_natCast_eq_emod (C 0 1) 4 (by norm_num)
  obtain ⟨c, hc, hc8⟩ := exists_natCast_eq_emod (C 1 1) 8 (by norm_num)
  have hk := htab a (by omega) b (by omega) c (by omega)
  set e := tab.getD (32 * a + 8 * b + c) (0, [], [])
  -- the induction step for a superlattice `C'` with `C = Dᵀ C' D`, `det D = ± 2`
  have hstep : ∀ (C' D : Matrix (Fin 2) (Fin 2) ℤ), C'ᵀ = C' → Dᵀ * C' * D = C → D.det ^ 2 = 4 →
      LocallyRepresents K C 2 := by
    intro C' D hC' hD hD4
    have hdet' : C.det = 4 * C'.det := by
      rw [← hD, det_mul, det_mul, det_transpose, ← hD4]; ring
    exact (ih C'.det.toNat (by omega) C' hC' rfl (by omega)).trans (locallyRepresents_of_eq D hD 2)
  unfold binChk2 at hk
  split at hk
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    simp only [ha, hb, hc] at hk
    obtain ⟨⟨h4', h8'⟩, hY'⟩ := hk
    have h4 := fun i j => Int.dvd_of_emod_eq_zero (h4' i j)
    have h8 := fun i => Int.dvd_of_emod_eq_zero (h8' i)
    have hY := fun i j => Int.dvd_of_emod_eq_zero (hY' i j)
    have hCb4 : ∀ i j, (4 : ℤ) ∣ C i j - bin (C 0 0 % 8) (C 0 1 % 4) (C 1 1 % 8) i j := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [bin, hs] <;> omega
    have hCb8 : ∀ i, (8 : ℤ) ∣ C i i - bin (C 0 0 % 8) (C 0 1 % 4) (C 1 1 % 8) i i := by
      intro i; fin_cases i <;> simp [bin] <;> omega
    refine hlift (mat52 e.2.1) (mat52 e.2.2) hY C hC (fun i j => ?_) fun i => ?_
    · have := dvd_sub (h4 i j) (hCb4 i j)
      simpa only [sub_sub_sub_cancel_right] using this
    · have := dvd_sub (h8 i) (hCb8 i)
      simpa only [sub_sub_sub_cancel_right] using this
  · simp only [decide_eq_true_eq] at hk
    simp only [ha, hb] at hk
    obtain ⟨q, hq⟩ : (4 : ℤ) ∣ C 0 0 := by omega
    obtain ⟨r, hr⟩ : (2 : ℤ) ∣ C 0 1 := by omega
    refine hstep !![q, r; r, C 1 1] !![2, 0; 0, 1] ?_ ?_ (by simp [det_fin_two])
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs] <;> linarith
  · simp only [decide_eq_true_eq] at hk
    simp only [hb, hc] at hk
    obtain ⟨q, hq⟩ : (4 : ℤ) ∣ C 1 1 := by omega
    obtain ⟨r, hr⟩ : (2 : ℤ) ∣ C 0 1 := by omega
    refine hstep !![C 0 0, r; r, q] !![1, 0; 0, 2] ?_ ?_ (by simp [det_fin_two])
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs] <;> linarith
  · simp only [decide_eq_true_eq] at hk
    simp only [ha, hb, hc] at hk
    obtain ⟨s, hs'⟩ : (4 : ℤ) ∣ C 0 0 + 2 * C 0 1 + C 1 1 := by omega
    obtain ⟨u, hu⟩ : (2 : ℤ) ∣ C 0 1 + C 1 1 := by omega
    refine hstep !![s, u; u, C 1 1] !![2, 0; -1, 1] ?_ ?_ (by simp [det_fin_two])
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs] <;> linarith

theorem w92_ok : ∀ a : ℕ, a < 8 → ∀ b : ℕ, b < 4 → ∀ c : ℕ, c < 8 →
    binChk2 J92 1 a b c (w92.getD (32 * a + 8 * b + c) (0, [], [])) = true := by
  decide +kernel

/-- **`K₉` represents every binary form of positive determinant over `ℤ₂`.** -/
theorem binary_two : ∀ (n : ℕ) (C : Matrix (Fin 2) (Fin 2) ℤ), Cᵀ = C → C.det.toNat = n → 0 < C.det →
    LocallyRepresents K9.gram C 2 :=
  binary_two_of_witnesses K9.gram J92 1 w92 w92_ok fun X Y hY C hC h4 h8 =>
    locallyRepresents_K9_two X Y (by simpa using hY) C hC h4 h8

/-! ### `p ≥ 5` -/

/-- **`K₉` represents every binary form over `ℤ_p`, `p ≥ 5`.** -/
theorem binary_large (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : Cᵀ = C) :
    LocallyRepresents K9.gram C p := by
  have hs : C 1 0 = C 0 1 := by simpa using congrFun (congrFun hC 0) 1
  -- `C ⊥ ⟨9⟩`, whose last diagonal entry is `9 · 1²`
  let g : Tern := ⟨C 0 0, C 0 1, C 1 1, 0, 0, 9⟩
  have hg : g.HasDiagSquareClass 9 p :=
    ⟨1, fun h => hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h),
      Or.inr (Or.inr ⟨0, by simp [g]⟩)⟩
  refine (square_K9 p hp h5 g hg).trans
    (locallyRepresents_of_eq (!![1, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℤ) ?_ p)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g, Tern.toMatrix, Matrix.mul_apply, Fin.sum_univ_three, hs]

/-- **`K₉` represents every binary form of positive determinant over every `ℤ_p`.** -/
theorem locallyRepresents_K9_binary (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : Cᵀ = C) (hdet : 0 < C.det)
    (p : ℕ) (hp : p.Prime) : LocallyRepresents K9.gram C p := by
  rcases prime_cases hp with rfl | rfl | h5
  · exact binary_two _ C hC rfl hdet
  · exact binary_three C hC
  · exact binary_large p hp h5 C hC

end KimKimOh.LocalBinary

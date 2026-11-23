import KimKimOh.Genus.Kko112Data
import KimKimOh.Local.Binary
import KimKimOh.Hosts

/-!
# `⟨1, 1, 2⟩ ⊥ A₂` is locally 2-universal

`locallyRepresents_kko112_binary`: `kko112 = ⟨1, 1, 2⟩ ⊥ A₂` represents every binary integral form
of positive determinant over every `ℤ_p`. In the coordinates of `M22 = hostForm 2 2 (-1) 2`:

* `p ≥ 5`: a binary `C` lies in the ternary `C ⊥ ⟨6⟩`, whose diagonal entry `6` is the
  determinant of `M22` (`square_of_hostForm`).
* `p = 3`: every residue class modulo 3 has a seed (`w22three`, checked by the kernel), and
  Hensel's lemma lifts it (`locallyRepresents_of_seed`).
* `p = 2`: 252 of the 256 residue classes modulo `(8, 4, 8)` have a witness `X` with
  `Xᵀ M22 Y ≡ 1 (mod 2)` (`w22two`), and the dyadic Hensel lemma applies to `M22` itself
  (`hensel_two`). The other four classes have an integral superlattice of index 2: induction on
  the determinant, as in `LocalBinary.binary_two`.
-/

namespace KimKimOh.Kko112

open Matrix Local LocalBinary

/-- `⟨1, 1, 2⟩ ⊥ A₂` on `Fin 5`. -/
abbrev M22 : Matrix (Fin 5) (Fin 5) ℤ := hostForm 2 2 (-1) 2

theorem kko112_embed : (embedMat Local.hostBasisK3)ᵀ * kko112.gram * embedMat Local.hostBasisK3 = M22 := by decide

/-! ### `p = 2` -/

theorem w22two_ok : ∀ a : ℕ, a < 8 → ∀ b : ℕ, b < 4 → ∀ c : ℕ, c < 8 →
    binChk2 M22 M22 a b c (w22two.getD (32 * a + 8 * b + c) (0, [], [])) = true := by
  decide +kernel

/-- **`M22` represents every binary form of positive determinant over `ℤ₂`.** -/
theorem binary_two : ∀ (n : ℕ) (C : Matrix (Fin 2) (Fin 2) ℤ), Cᵀ = C → C.det.toNat = n → 0 < C.det →
    LocallyRepresents M22 C 2 :=
  binary_two_of_witnesses M22 M22 M22 w22two w22two_ok fun X Y hY C hC h4 h8 =>
    hensel_two M22 (hostForm_transpose _ _ _ _) C hC X Y h4 h8 hY

/-! ### `p = 3` -/

/-- The `2 × 5` matrix with the entries of a list, row-major. -/
def mat25 (l : List ℤ) : Matrix (Fin 2) (Fin 5) ℤ := Matrix.of fun i j => l.getD (5 * i.val + j.val) 0

/-- The test of a seed at 3: `Xᵀ M22 X ≡ [[a, b], [b, c]]` and `Y M22 X ≡ 1 (mod 3)`. -/
def chk3 (a b c : ℤ) (w : List ℤ × List ℤ) : Bool :=
  decide (∀ i j, ((mat52 w.1)ᵀ * M22 * mat52 w.1 - bin a b c) i j % 3 = 0) &&
    decide (∀ i j, (mat25 w.2 * M22 * mat52 w.1 - (1 : Matrix (Fin 2) (Fin 2) ℤ)) i j % 3 = 0)

theorem w22three_ok : ∀ a : ℕ, a < 3 → ∀ b : ℕ, b < 3 → ∀ c : ℕ, c < 3 →
    chk3 a b c (w22three.getD (9 * a + 3 * b + c) ([], [])) = true := by
  decide +kernel

/-- **`M22` represents every binary form over `ℤ₃`.** -/
theorem binary_three (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : Cᵀ = C) : LocallyRepresents M22 C 3 := by
  have hs : C 1 0 = C 0 1 := by simpa using congrFun (congrFun hC 0) 1
  obtain ⟨a, ha, ha3⟩ := exists_natCast_eq_emod (C 0 0) 3 (by norm_num)
  obtain ⟨b, hb, hb3⟩ := exists_natCast_eq_emod (C 0 1) 3 (by norm_num)
  obtain ⟨c, hc, hc3⟩ := exists_natCast_eq_emod (C 1 1) 3 (by norm_num)
  have hk := w22three_ok a (by omega) b (by omega) c (by omega)
  set w := w22three.getD (9 * a + 3 * b + c) ([], [])
  simp only [chk3, Bool.and_eq_true, decide_eq_true_eq] at hk
  rw [ha, hb, hc] at hk
  obtain ⟨hX', hY'⟩ := hk
  have hX : ∀ i j, (3 : ℤ) ∣ ((mat52 w.1)ᵀ * M22 * mat52 w.1 - C) i j := by
    intro i j
    have h1 := Int.dvd_of_emod_eq_zero (hX' i j)
    have h2 : (3 : ℤ) ∣ (bin (C 0 0 % 3) (C 0 1 % 3) (C 1 1 % 3) - C) i j := by
      fin_cases i <;> fin_cases j <;> simp [bin, hs] <;> omega
    have := dvd_add h1 h2
    simpa only [Matrix.sub_apply, sub_add_sub_cancel] using this
  have hY : ∀ i j, (3 : ℤ) ∣ (mat25 w.2 * M22 * mat52 w.1 - (1 : Matrix (Fin 2) (Fin 2) ℤ)) i j :=
    fun i j => Int.dvd_of_emod_eq_zero (hY' i j)
  have := Fact.mk Nat.prime_three
  refine OddPrime.locallyRepresents_of_seed (by norm_num) (hostForm_transpose _ _ _ _) hC
    ⟨(mat52 w.1).map (Int.castRingHom (ZMod 3)), (mat25 w.2).map (Int.castRingHom (ZMod 3)), ?_, ?_⟩
  · rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    exact OddPrime.dvd_sub_iff_map_eq.mp (by exact_mod_cast hX)
  · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_one (Int.castRingHom (ZMod 3)) (map_zero _) (map_one _)]
    exact OddPrime.dvd_sub_iff_map_eq.mp (by exact_mod_cast hY)

/-! ### `p ≥ 5` -/

/-- **`M22` represents every binary form over `ℤ_p`, `p ≥ 5`.** -/
theorem binary_large (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : Cᵀ = C) :
    LocallyRepresents M22 C p := by
  have hs : C 1 0 = C 0 1 := by simpa using congrFun (congrFun hC 0) 1
  let g : Tern := ⟨C 0 0, C 0 1, C 1 1, 0, 0, 6⟩
  have hg : g.HasDiagSquareClass 6 p :=
    ⟨1, fun h => hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h),
      Or.inr (Or.inr ⟨0, by simp [g]⟩)⟩
  have he : (1 : Matrix (Fin 5) (Fin 5) ℤ)ᵀ * M22 * 1 = hostForm 2 2 (-1) 2 := by simp
  refine (OddPrime.square_of_hostForm he (by decide) (by norm_num) p hp h5 g hg).trans
    (locallyRepresents_of_eq (!![1, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℤ) ?_ p)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g, Tern.toMatrix, Matrix.mul_apply, Fin.sum_univ_three, hs]

/-- **`⟨1, 1, 2⟩ ⊥ A₂` represents every binary form of positive determinant over every `ℤ_p`.** -/
theorem locallyRepresents_kko112_binary (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : Cᵀ = C) (hdet : 0 < C.det)
    (p : ℕ) (hp : p.Prime) : LocallyRepresents kko112.gram C p := by
  refine .of_host (embedMat Local.hostBasisK3) kko112_embed ?_
  rcases prime_cases hp with rfl | rfl | h5
  · exact binary_two _ C hC rfl hdet
  · exact binary_three C hC
  · exact binary_large p hp h5 C hC

end KimKimOh.Kko112

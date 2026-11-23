import KimKimOh.Genus.K3K9Symbols
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal
import QuadFormsKB.Siegel.KneserMass
import QuadFormsKB.Literature.Watson1963.GenusRep

/-!
# Class number 1 of `K₃` and `K₉`, and the local–global principle for them

The Conway–Sloane mass formula (`mass_eq_stdMass_mul_symbols_unconditional`), with the local
symbols of `K3K9Symbols`, gives the masses `1/576` and `1/192` of the genera of `K₃ = A₂ ⊥ I₃` and
`K₉ = A₂ ⊥ ⟨3⟩ ⊥ I₂`. These equal `1/|Aut K₃|` and `1/|Aut K₉|`, so each genus has one class
(`genusClasses_eq_of_sum_eq_mass`). With the genus representation theorem
(`Watson1963.rep_of_encard_le_one`): a positive definite form represented by `K₃` (or `K₉`) over
every `ℤ_p` is represented by it over `ℤ`.
-/

open Matrix

namespace KimKimOh.Genera

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass QuadFormsKB.Siegel.Kneser

theorem primeFactors_six : (2 * (3 : ℤ)).natAbs.primeFactors = {2, 3} := by
  rw [show (2 * (3 : ℤ)).natAbs = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  rfl

theorem primeFactors_eighteen : (2 * (9 : ℤ)).natAbs.primeFactors = {2, 3} := by
  rw [show (2 * (9 : ℤ)).natAbs = 2 * 3 ^ 2 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
  rfl

/-- **The mass of the genus of `K₃` is `1/576`** (Conway–Sloane mass formula). -/
theorem mass_g3 : Siegel.mass (ofMatrixZ g3) = 1 / 576 := by
  have hsupp2 : tau3.SupportedBelow 1 := fun k hk => by simp [tau3, show k ≠ 0 by omega]
  have hsupp3 : ∀ k, 2 ≤ k → sig3 k = OddFactor.trivial := fun k hk => by
    simp [sig3, show k ≠ 0 by omega, show k ≠ 1 by omega]
  rw [mass_eq_stdMass_mul_symbols_unconditional (by norm_num) g3_symm posDef_g3 tau3 1
    isTwoSymbolOf_g3 hsupp2 (fun _ => sig3) (fun _ => 2) ?_]
  · rw [g3_det, primeFactors_six, Finset.prod_insert (by decide), Finset.prod_singleton, ite_eq_left rfl,
      ite_eq_right (by norm_num), pMassTwo_tau3, pMassOdd_sig3, stdP_two_five, stdP_three_five, stdMass_table_5]
    norm_num
  · intro p hp _ hdvd
    rw [g3_det] at hdvd
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by exact_mod_cast hdvd)
    subst hp3
    exact ⟨isOddSymbolOf_g3, hsupp3⟩

/-- **The mass of the genus of `K₉` is `1/192`** (Conway–Sloane mass formula). -/
theorem mass_g9 : Siegel.mass (ofMatrixZ g9) = 1 / 192 := by
  have hsupp2 : tau9.SupportedBelow 1 := fun k hk => by simp [tau9, show k ≠ 0 by omega]
  have hsupp3 : ∀ k, 2 ≤ k → sig9 k = OddFactor.trivial := fun k hk => by
    simp [sig9, show k ≠ 0 by omega, show k ≠ 1 by omega]
  rw [mass_eq_stdMass_mul_symbols_unconditional (by norm_num) g9_symm posDef_g9 tau9 1
    isTwoSymbolOf_g9 hsupp2 (fun _ => sig9) (fun _ => 2) ?_]
  · rw [g9_det, primeFactors_eighteen, Finset.prod_insert (by decide), Finset.prod_singleton, ite_eq_left rfl,
      ite_eq_right (by norm_num), pMassTwo_tau9, pMassOdd_sig9, stdP_two_five, stdP_three_five, stdMass_table_5]
    norm_num
  · intro p hp _ hdvd
    rw [g9_det] at hdvd
    have hp3 : p ∣ 9 := by exact_mod_cast hdvd
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (hp.dvd_of_dvd_pow (n := 2) (by simpa using hp3))
    subst hp3
    exact ⟨isOddSymbolOf_g9, hsupp3⟩

/-- **`K₃` is alone in its genus.** -/
theorem encard_genusClasses_g3 : (genusClasses (ofMatrixZ g3)).encard ≤ 1 := by
  have h := genusClasses_eq_of_sum_eq_mass posDef_g3 (fun _ : Fin 1 => ofMatrixZ g3)
    (fun _ => SameGenus.refl _) (fun i j _ => Subsingleton.elim i j)
    (by rw [Fin.sum_univ_one, card_aut_g3, mass_g3]; norm_num)
  rw [h, Set.range_const, Set.encard_singleton]

/-- **`K₉` is alone in its genus.** -/
theorem encard_genusClasses_g9 : (genusClasses (ofMatrixZ g9)).encard ≤ 1 := by
  have h := genusClasses_eq_of_sum_eq_mass posDef_g9 (fun _ : Fin 1 => ofMatrixZ g9)
    (fun _ => SameGenus.refl _) (fun i j _ => Subsingleton.elim i j)
    (by rw [Fin.sum_univ_one, card_aut_g9, mass_g9]; norm_num)
  rw [h, Set.range_const, Set.encard_singleton]

/-- **Local–global principle for `K₃`**: a positive definite form represented by `K₃` over every
`ℤ_p` is represented by `K₃`. -/
theorem rep_g3 {v : ℕ} {φ : QuadForm ℤ v} (hφ : IntQF.PosDef φ)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], Watson1963.RepOver ℤ_[p] (ofMatrixZ g3) φ) :
    Watson1963.Rep (ofMatrixZ g3) φ :=
  Watson1963.rep_of_encard_le_one posDef_g3 hφ hloc encard_genusClasses_g3

/-- **Local–global principle for `K₉`**: a positive definite form represented by `K₉` over every
`ℤ_p` is represented by `K₉`. -/
theorem rep_g9 {v : ℕ} {φ : QuadForm ℤ v} (hφ : IntQF.PosDef φ)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], Watson1963.RepOver ℤ_[p] (ofMatrixZ g9) φ) :
    Watson1963.Rep (ofMatrixZ g9) φ :=
  Watson1963.rep_of_encard_le_one posDef_g9 hφ hloc encard_genusClasses_g9

end KimKimOh.Genera

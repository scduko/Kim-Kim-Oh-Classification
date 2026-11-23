import KimKimOh.Local.Precision
import KimKimOh.Hosts

/-!
# The diagonal bases at 2 and 3 (§2)

In a root basis `a, b` of `A₂` with `(a, b) = -1`:

* `a, a + 2b` are orthogonal of norms `2, 6`, and span a sublattice of index 2;
* for a unit vector `e` orthogonal to `A₂`, the vectors `e + a, e + b, e - a - b` are orthogonal
  of norm 3, and span a sublattice of index 3 in `ℤe ⊥ A₂`.

This gives sublattices `Pᵀ K P = J` with `J` diagonal:

| | `K₃` | `K₉` |
| --- | --- | --- |
| at 2 | `⟨1, 1, 3, 3, 3⟩` (`J32`) | `⟨1, 3, 3, 3, 3⟩` (`J92`) |
| at 3 | `⟨1, 1, 1, 2, 6⟩` (`J33`) | `⟨1, 1, 2, 3, 6⟩` (`J93`) |

A local representation by `J` is one by `K` (`LocallyRepresents.of_host`), so
`lem:local-precision` for `J` gives local criteria for `K₃` and `K₉`
(`locallyRepresents_K3_two`, …). The paper notes that these sublattices are the whole lattice
over `ℤ₂` and `ℤ₃` respectively; only the inclusion is needed here.
-/

namespace KimKimOh.Local

open Matrix Precision

/-- `⟨1, 1, 3, 3, 3⟩`. -/
def J32 : Matrix (Fin 5) (Fin 5) ℤ := diagonal ![1, 1, 3, 3, 3]
/-- `⟨1, 3, 3, 3, 3⟩`. -/
def J92 : Matrix (Fin 5) (Fin 5) ℤ := diagonal ![1, 3, 3, 3, 3]
/-- `⟨1, 1, 1, 2, 6⟩`. -/
def J33 : Matrix (Fin 5) (Fin 5) ℤ := diagonal ![1, 1, 1, 2, 6]
/-- `⟨1, 1, 2, 3, 6⟩`. -/
def J93 : Matrix (Fin 5) (Fin 5) ℤ := diagonal ![1, 1, 2, 3, 6]

/-- The columns `e₁, e₂, e₃ + a, e₃ + b, e₃ - a - b` in `K₃ = I₃ ⊥ A₂`. -/
def P32 : Matrix (Fin 3 ⊕ Fin 2) (Fin 5) ℤ :=
  Matrix.of fun i j => match i, j with
    | .inl 0, 0 => 1
    | .inl 1, 1 => 1
    | .inl 2, 2 => 1 | .inl 2, 3 => 1 | .inl 2, 4 => 1
    | .inr 0, 2 => 1 | .inr 1, 3 => 1 | .inr 0, 4 => -1 | .inr 1, 4 => -1
    | _, _ => 0

/-- The columns `e₁, e₂, e₃, a, a + 2b` in `K₃`. -/
def P33 : Matrix (Fin 3 ⊕ Fin 2) (Fin 5) ℤ :=
  Matrix.of fun i j => match i, j with
    | .inl 0, 0 => 1 | .inl 1, 1 => 1 | .inl 2, 2 => 1
    | .inr 0, 3 => 1 | .inr 0, 4 => 1 | .inr 1, 4 => 2
    | _, _ => 0

/-- The columns `e₁, e₂ + a, e₂ + b, e₂ - a - b, f` in `K₉ = I₂ ⊥ A₂ ⊥ ⟨3⟩`. -/
def P92 : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) (Fin 5) ℤ :=
  Matrix.of fun i j => match i, j with
    | .inl (.inl 0), 0 => 1
    | .inl (.inl 1), 1 => 1 | .inl (.inl 1), 2 => 1 | .inl (.inl 1), 3 => 1
    | .inl (.inr 0), 1 => 1 | .inl (.inr 1), 2 => 1
    | .inl (.inr 0), 3 => -1 | .inl (.inr 1), 3 => -1
    | .inr 0, 4 => 1
    | _, _ => 0

/-- The columns `e₁, e₂, a, f, a + 2b` in `K₉`. -/
def P93 : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) (Fin 5) ℤ :=
  Matrix.of fun i j => match i, j with
    | .inl (.inl 0), 0 => 1 | .inl (.inl 1), 1 => 1
    | .inl (.inr 0), 2 => 1 | .inr 0, 3 => 1
    | .inl (.inr 0), 4 => 1 | .inl (.inr 1), 4 => 2
    | _, _ => 0

theorem P32_spec : P32ᵀ * K3.gram * P32 = J32 := by decide +kernel
theorem P33_spec : P33ᵀ * K3.gram * P33 = J33 := by decide +kernel
theorem P92_spec : P92ᵀ * K9.gram * P92 = J92 := by decide +kernel
theorem P93_spec : P93ᵀ * K9.gram * P93 = J93 := by decide +kernel

/-- `J ≡ 1 (mod 2)` for the odd diagonals at 2. -/
theorem J32_odd : ∀ i j, (2 : ℤ) ∣ J32 i j - (1 : Matrix (Fin 5) (Fin 5) ℤ) i j := by decide
theorem J92_odd : ∀ i j, (2 : ℤ) ∣ J92 i j - (1 : Matrix (Fin 5) (Fin 5) ℤ) i j := by decide

/-- `J E = 3` over `ZMod 3ᴷ` for the diagonals at 3, with `E = 3 J⁻¹`. -/
theorem J33_dual (K : ℕ) : ∃ E : Matrix (Fin 5) (Fin 5) (ZMod (3 ^ K)), Eᵀ = E ∧
    J33.map (Int.castRingHom (ZMod (3 ^ K))) * E = (3 : ZMod (3 ^ K)) • 1 := by
  set i2 : ZMod (3 ^ K) := (((3 ^ K + 1) / 2 : ℕ) : ZMod (3 ^ K))
  have hi2 := two_mul_inv K
  refine ⟨diagonal ![3, 3, 3, 3 * i2, i2], diagonal_transpose _, ?_⟩
  rw [J33, diagonal_map (map_zero _), diagonal_mul_diagonal, ← diagonal_one, ← diagonal_smul]
  congr 1
  funext i
  fin_cases i <;> simp <;> linear_combination 3 * hi2

theorem J93_dual (K : ℕ) : ∃ E : Matrix (Fin 5) (Fin 5) (ZMod (3 ^ K)), Eᵀ = E ∧
    J93.map (Int.castRingHom (ZMod (3 ^ K))) * E = (3 : ZMod (3 ^ K)) • 1 := by
  set i2 : ZMod (3 ^ K) := (((3 ^ K + 1) / 2 : ℕ) : ZMod (3 ^ K))
  have hi2 := two_mul_inv K
  refine ⟨diagonal ![3, 3, 3 * i2, 1, i2], diagonal_transpose _, ?_⟩
  rw [J93, diagonal_map (map_zero _), diagonal_mul_diagonal, ← diagonal_one, ← diagonal_smul]
  congr 1
  funext i
  fin_cases i <;> simp <;> linear_combination 3 * hi2

variable {m : ℕ}

/-- The local criterion at 2 for `K₃`. -/
theorem locallyRepresents_K3_two (X Y : Matrix (Fin 5) (Fin m) ℤ)
    (hY : ∀ i j, (2 : ℤ) ∣ (Xᵀ * Y) i j - (1 : Matrix (Fin m) (Fin m) ℤ) i j)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : Cᵀ = C)
    (h4 : ∀ i j, (4 : ℤ) ∣ (Xᵀ * J32 * X) i j - C i j)
    (h8 : ∀ i, (8 : ℤ) ∣ (Xᵀ * J32 * X) i i - C i i) : LocallyRepresents K3.gram C 2 :=
  .of_host P32 P32_spec
    (locallyRepresents_of_precision_two J32 (diagonal_transpose _) J32_odd X Y hY C hC h4 h8)

/-- The local criterion at 2 for `K₉`. -/
theorem locallyRepresents_K9_two (X Y : Matrix (Fin 5) (Fin m) ℤ)
    (hY : ∀ i j, (2 : ℤ) ∣ (Xᵀ * Y) i j - (1 : Matrix (Fin m) (Fin m) ℤ) i j)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : Cᵀ = C)
    (h4 : ∀ i j, (4 : ℤ) ∣ (Xᵀ * J92 * X) i j - C i j)
    (h8 : ∀ i, (8 : ℤ) ∣ (Xᵀ * J92 * X) i i - C i i) : LocallyRepresents K9.gram C 2 :=
  .of_host P92 P92_spec
    (locallyRepresents_of_precision_two J92 (diagonal_transpose _) J92_odd X Y hY C hC h4 h8)

/-- The local criterion at 3 for `K₃`. -/
theorem locallyRepresents_K3_three (X Y : Matrix (Fin 5) (Fin m) ℤ)
    (hY : ∀ i j, (3 : ℤ) ∣ (Xᵀ * Y - (1 : Matrix (Fin m) (Fin m) ℤ)) i j)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : Cᵀ = C)
    (h9 : ∀ i j, (9 : ℤ) ∣ (C - Xᵀ * J33 * X) i j) : LocallyRepresents K3.gram C 3 :=
  .of_host P33 P33_spec
    (locallyRepresents_of_precision_three J33 (diagonal_transpose _) J33_dual X Y hY C hC h9)

/-- The local criterion at 3 for `K₉`. -/
theorem locallyRepresents_K9_three (X Y : Matrix (Fin 5) (Fin m) ℤ)
    (hY : ∀ i j, (3 : ℤ) ∣ (Xᵀ * Y - (1 : Matrix (Fin m) (Fin m) ℤ)) i j)
    (C : Matrix (Fin m) (Fin m) ℤ) (hC : Cᵀ = C)
    (h9 : ∀ i j, (9 : ℤ) ∣ (C - Xᵀ * J93 * X) i j) : LocallyRepresents K9.gram C 3 :=
  .of_host P93 P93_spec
    (locallyRepresents_of_precision_three J93 (diagonal_transpose _) J93_dual X Y hY C hC h9)

end KimKimOh.Local

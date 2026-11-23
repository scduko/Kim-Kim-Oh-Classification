import KimKimOh.Lattices

/-!
# The quinary lattices `K_j` (`eq:pairs`)

`L₆ = K₃ ⊥ ⟨2⟩` with `K₃ = I₃ ⊥ A₂`, and `L₉ = K₉ ⊥ ⟨1⟩` with `K₉ = I₂ ⊥ A₂ ⊥ ⟨3⟩`, where
`j = det K_j` (`L6_represents_K3_line`, `L9_represents_K9_line`).

`represents_orthSum_line` is the correction step of the strategy: a representation of
`C = G - s λλᵀ` by `K` extends, by the coordinate `λ` on the line, to a representation
of `G` by `K ⊥ ⟨s⟩`.

`kko112 = ⟨1,1,2⟩ ⊥ A₂` and `kko113 = ⟨1,1,3⟩ ⊥ A₂` are the complements of a unit vector in `L₆`
and `L₉`. Their 2-universality (Kim–Kim–Oh, Theorem 1; `kko112_universal`, `kko113_universal` in
`KimKimOh/Genus/`) handles the ternaries of minimum 1. Kim–Kim–Oh write `A₂ = [2, 1, 2]`, which
is isometric to `rootA2`.
-/

namespace KimKimOh

open Matrix GramLattice

/-- The line `⟨s⟩`. -/
def line (s : ℤ) (hs : 0 < s) : GramLattice (Fin 1) :=
  diagLattice (fun _ => s) fun _ => hs

/-- `K₃ = I₃ ⊥ A₂`. -/
def K3 : GramLattice (Fin 3 ⊕ Fin 2) := (stdLattice 3).orthSum rootA2

/-- `K₉ = I₂ ⊥ A₂ ⊥ ⟨3⟩`. -/
def K9 : GramLattice ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) :=
  ((stdLattice 2).orthSum rootA2).orthSum lattice3

/-- `⟨1, 1, 2⟩ ⊥ A₂`, the complement of a unit vector in `L₆`. -/
def kko112 : GramLattice (Fin 3 ⊕ Fin 2) :=
  (diagLattice ![1, 1, 2] (by decide)).orthSum rootA2

/-- `⟨1, 1, 3⟩ ⊥ A₂`, the complement of a unit vector in `L₉`. -/
def kko113 : GramLattice (Fin 3 ⊕ Fin 2) :=
  (diagLattice ![1, 1, 3] (by decide)).orthSum rootA2

/-- **The correction step.** If `K` represents `G - s λλᵀ`, then `K ⊥ ⟨s⟩` represents `G`:
the line coordinate of the embedding is `λ`. -/
theorem represents_orthSum_line {ι κ : Type*} [Fintype ι] [Fintype κ] (K : GramLattice ι)
    {s : ℤ} (hs : 0 < s) (S : GramLattice κ) (lam : κ → ℤ) (Y : Matrix ι κ ℤ)
    (hY : Yᵀ * K.gram * Y = S.gram - s • vecMulVec lam lam) :
    (K.orthSum (line s hs)).Represents S := by
  refine ⟨Matrix.of fun p k => Sum.elim (fun a => Y a k) (fun _ => lam k) p, ?_⟩
  have h : S.gram = Yᵀ * K.gram * Y + s • vecMulVec lam lam := by rw [hY]; abel
  rw [h]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, line, diagLattice, vecMulVec, Function.swap]
  ring

/-! ### `eq:pairs` -/

/-- `K₃ ⊥ ⟨2⟩ ⊆ L₆`: `A₁ = ⟨2⟩`. -/
theorem L6_represents_K3_line : L6.Represents (K3.orthSum (line 2 two_pos)) := by
  refine ⟨Matrix.of fun p q => ?_, ?_⟩
  · exact match p, q with
      | .inl (.inl a), .inl (.inl b) => if a = b then 1 else 0
      | .inr a, .inl (.inr b) => if a = b then 1 else 0
      | .inl (.inr _), .inr _ => 1
      | _, _ => 0
  · decide

/-- `K₉ ⊥ ⟨1⟩ ⊆ L₉`: `I₃ = I₂ ⊥ ⟨1⟩`. -/
theorem L9_represents_K9_line : L9.Represents (K9.orthSum (line 1 one_pos)) := by
  refine ⟨Matrix.of fun p q => ?_, ?_⟩
  · exact match p, q with
      | .inl (.inl a), .inl (.inl (.inl b)) => if (a : ℕ) = b then 1 else 0
      | .inl (.inl 2), .inr _ => 1
      | .inl (.inr a), .inl (.inl (.inr b)) => if a = b then 1 else 0
      | .inr _, .inl (.inr _) => 1
      | _, _ => 0
  · decide

end KimKimOh

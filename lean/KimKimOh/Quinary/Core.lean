import KimKimOh.Roots
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Proposition 5.1 (`prop:exception`): `I₆ ⊥ A₂` does not represent `Λ₁₁₇`

This file proves, at the level of Gram matrices, that no integer matrix `X` satisfies
`Xᵀ G X = T`, where `G` is the Gram matrix of `I₆ ⊥ A₂` and `T` is the quinary Gram matrix
of Proposition 5.1 (`not_represents`).

The argument follows the paper. Write `a, b, c, x, y` for the images of the basis of `T`.

1. A vector of norm 2 lies in `I₆` or in `A₂` (`root_split`). The pairings `-1` keep
   the chain `a, b, c` in one summand, and three roots of `A₂` cannot have the Gram
   matrix of `A₃`, since their Gram determinant vanishes (`not_chain_A2`).
2. In `I₆` every root is `±eᵢ ± eⱼ` (`root_support`). After three signed permutations
   (`root_to_e01`, `root_to_e12`, `root_to_e23_or_n01`, checked by the kernel) `a = e₀ - e₁`,
   `b = e₁ - e₂`, and `c = e₂ - e₃` or `c = -e₀ - e₁` (`normalize_chain`).
3. The second choice makes `(a - c, x) = 2x₀` even, while it equals `1`. In the first,
   the pairings force `x = (t+1, t, t, t) + u` and `y = (s+1, s+1, s, s) + v` with
   `u, v` in `K = I₂ ⊥ A₂`, `t, s ∈ {0, -1}`, `Q(v) = 5`, and either `Q(u) = 5` with
   `(u, v) ∈ {-2, -1}` or `Q(u) = 3` with `(u, v) ∈ {0, -3}`. Kernel checks on the vectors
   of norm at most 5 in `K` exclude both (`final_arith`).
-/

namespace KimKimOh.Quinary

open Matrix

/-! ### The forms -/

/-- Vectors of `I₆`. -/
abbrev V6 := Fin 6 → ℤ

/-- The inner product of `I₆`, written out so that the kernel evaluates it quickly. -/
def dot6 (u v : V6) : ℤ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5

theorem dot6_eq_sum (u v : V6) : dot6 u v = ∑ m, u m * v m := by
  simp [dot6, Fin.sum_univ_six]

/-- The Gram matrix of `A₂`. -/
def gramA2 : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of ![![2, -1], ![-1, 2]]

/-- The Gram matrix of `I₆ ⊥ A₂`. -/
def gramL : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℤ :=
  fromBlocks 1 0 0 gramA2

/-- The Gram matrix of the quinary lattice `Λ₁₁₇` of Proposition 5.1. -/
def gramT : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of ![![ 2, -1,  0,  1,  0],
              ![-1,  2, -1,  0,  1],
              ![ 0, -1,  2,  0,  0],
              ![ 1,  0,  0,  6, -1],
              ![ 0,  1,  0, -1,  7]]

@[simp] theorem dot6_zero_left (v : V6) : dot6 0 v = 0 := by simp [dot6]
@[simp] theorem dot6_zero_right (v : V6) : dot6 v 0 = 0 := by simp [dot6]
theorem dot6_self_nonneg (u : V6) : 0 ≤ dot6 u u := by
  rw [dot6_eq_sum]; exact Finset.sum_nonneg fun m _ => mul_self_nonneg (u m)

theorem eq_zero_of_dot6_self_eq_zero {u : V6} (h : dot6 u u = 0) : u = 0 := by
  rw [dot6_eq_sum, Finset.sum_mul_self_eq_zero_iff] at h
  exact funext fun m => h m (Finset.mem_univ m)

/-! ### Embeddings of `T` -/

/-- The pairing equations for the images `(uᵢ, vᵢ) ∈ I₆ ⊥ A₂` of the basis of `T`. -/
def IsEmbedding (u : Fin 5 → V6) (v : Fin 5 → Fin 2 → ℤ) : Prop :=
  ∀ i j, dot6 (u i) (u j) + bilinA2 (v i) (v j) = gramT i j

/-- An entry of `Xᵀ G X` is the pairing of two columns of `X`. -/
theorem gram_entry (X : Matrix (Fin 6 ⊕ Fin 2) (Fin 5) ℤ) (i j : Fin 5) :
    (Xᵀ * gramL * X) i j =
      dot6 (fun m => X (.inl m) i) (fun m => X (.inl m) j) +
        bilinA2 (fun k => X (.inr k) i) (fun k => X (.inr k) j) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, gramL, gramA2, Matrix.one_apply, dot6, bilinA2,
    Fin.sum_univ_two, Fin.sum_univ_six]
  ring

theorem isEmbedding_of_eq {X : Matrix (Fin 6 ⊕ Fin 2) (Fin 5) ℤ}
    (hX : Xᵀ * gramL * X = gramT) :
    IsEmbedding (fun i m => X (.inl m) i) (fun i k => X (.inr k) i) := fun i j => by
  rw [← gram_entry, hX]

/-! ### Roots -/

/-- A vector of norm 2 of `I₆ ⊥ A₂` lies in one of the two summands. -/
theorem root_split (u : V6) (v : Fin 2 → ℤ) (h : dot6 u u + bilinA2 v v = 2) :
    (v = 0 ∧ dot6 u u = 2) ∨ (u = 0 ∧ bilinA2 v v = 2) := by
  have hu := dot6_self_nonneg u
  have hv := bilinA2_self v
  have hk0 := a2_quad_nonneg (v 0) (v 1)
  rcases (show v 0 ^ 2 - v 0 * v 1 + v 1 ^ 2 = 0 ∨ v 0 ^ 2 - v 0 * v 1 + v 1 ^ 2 = 1 by
    omega) with hk | hk
  · exact Or.inl ⟨a2_quad_eq_zero hk, by omega⟩
  · exact Or.inr ⟨eq_zero_of_dot6_self_eq_zero (by omega), by omega⟩

/-- Three roots of `A₂` cannot have the Gram matrix of `A₃`: the Gram determinant of three
vectors in a plane vanishes, while `det A₃ = 4`. -/
theorem not_chain_A2 (p q r : Fin 2 → ℤ) (hp : bilinA2 p p = 2) (hq : bilinA2 q q = 2)
    (hr : bilinA2 r r = 2) (hpq : bilinA2 p q = -1) (hpr : bilinA2 p r = 0) (hqr : bilinA2 q r = -1) :
    False := by
  have key : bilinA2 p p * (bilinA2 q q * bilinA2 r r - bilinA2 q r * bilinA2 q r)
      - bilinA2 p q * (bilinA2 p q * bilinA2 r r - bilinA2 q r * bilinA2 p r)
      + bilinA2 p r * (bilinA2 p q * bilinA2 q r - bilinA2 q q * bilinA2 p r) = 0 := by
    simp only [bilinA2]; ring
  rw [hp, hq, hr, hpq, hpr, hqr] at key
  norm_num at key

/-- `vec2 i j α β = α eᵢ + β eⱼ`. -/
def vec2 (i j : Fin 6) (α β : ℤ) : V6 :=
  fun m => (if m = i then α else 0) + (if m = j then β else 0)

/-! ### Signed permutations -/

/-- The signed permutation `(act σ ε v) m = ε m * v (σ m)`; it is an isometry of `I₆` when
every `ε m` is `±1`. -/
def act (σ : Equiv.Perm (Fin 6)) (ε : Fin 6 → ℤ) (v : V6) : V6 :=
  fun m => ε m * v (σ m)

theorem dot6_act (σ : Equiv.Perm (Fin 6)) (ε : Fin 6 → ℤ) (hε : ∀ m, ε m * ε m = 1)
    (u v : V6) : dot6 (act σ ε u) (act σ ε v) = dot6 u v := by
  rw [dot6_eq_sum, dot6_eq_sum]
  calc ∑ m, act σ ε u m * act σ ε v m = ∑ m, u (σ m) * v (σ m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [act]
        linear_combination (u (σ m) * v (σ m)) * hε m
    _ = ∑ m, u m * v m := Equiv.sum_comp σ (fun m => u m * v m)

theorem IsEmbedding.act {u : Fin 5 → V6} {v : Fin 5 → Fin 2 → ℤ} (h : IsEmbedding u v)
    (σ : Equiv.Perm (Fin 6)) (ε : Fin 6 → ℤ) (hε : ∀ m, ε m * ε m = 1) :
    IsEmbedding (fun i => act σ ε (u i)) v := fun i j => by
  simp only [dot6_act σ ε hε]
  exact h i j

/-- `e₀ - e₁`. With `e₁ - e₂`, and `e₂ - e₃` or `-e₀ - e₁`, the normal forms of the chain
`a, b, c`. -/
def e01 : V6 := ![1, -1, 0, 0, 0, 0]
/-- `e₁ - e₂`. -/
def e12 : V6 := ![0, 1, -1, 0, 0, 0]
/-- `e₂ - e₃`. -/
def e23 : V6 := ![0, 0, 1, -1, 0, 0]
/-- `-e₀ - e₁`. -/
def n01 : V6 := ![-1, -1, 0, 0, 0, 0]

@[simp] theorem dot6_e01 (x : V6) : dot6 e01 x = x 0 - x 1 := by simp [dot6, e01]; ring
@[simp] theorem dot6_e12 (x : V6) : dot6 e12 x = x 1 - x 2 := by simp [dot6, e12]; ring
@[simp] theorem dot6_e23 (x : V6) : dot6 e23 x = x 2 - x 3 := by simp [dot6, e23]; ring
@[simp] theorem dot6_n01 (x : V6) : dot6 n01 x = -x 0 - x 1 := by simp [dot6, n01]; ring

/-- The permutation sending `0 ↦ i` and `1 ↦ j`, for `i ≠ j`. -/
def σ₁ (i j : Fin 6) : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j)

/-- The signs carrying `α eᵢ + β eⱼ` to `e₀ - e₁` after `σ₁ i j`. -/
def ε₁ (α β : ℤ) : Fin 6 → ℤ :=
  fun m => if m = 0 then α else if m = 1 then -β else 1

/-- Kernel check: a signed permutation carries any root to `e₀ - e₁`. -/
theorem root_to_e01 : ∀ i j : Fin 6, i ≠ j → ∀ α ∈ ([1, -1] : List ℤ), ∀ β ∈ ([1, -1] : List ℤ),
    (∀ m, ε₁ α β m * ε₁ α β m = 1) ∧ act (σ₁ i j) (ε₁ α β) (vec2 i j α β) = e01 := by
  decide +kernel

/-- Signed permutations fixing `e₀ - e₁`. -/
def cands₂ : List (Equiv.Perm (Fin 6) × (Fin 6 → ℤ)) :=
  ([2, 3, 4, 5] : List (Fin 6)).flatMap fun m => ([1, -1] : List ℤ).flatMap fun β =>
    [(Equiv.swap 2 m, fun p => if p = 2 then β else 1),
     (Equiv.swap 0 1 * Equiv.swap 2 m,
       fun p => if p = 0 ∨ p = 1 then -1 else if p = 2 then β else 1)]

/-- Kernel check: a root `b` with `(e₀ - e₁, b) = -1` is carried to `e₁ - e₂` by a signed
permutation fixing `e₀ - e₁`. -/
theorem root_to_e12 : ∀ k l : Fin 6, k ≠ l → ∀ γ ∈ ([1, -1] : List ℤ), ∀ δ ∈ ([1, -1] : List ℤ),
    dot6 e01 (vec2 k l γ δ) = -1 →
      ∃ g ∈ cands₂, (∀ m, g.2 m * g.2 m = 1) ∧ act g.1 g.2 e01 = e01 ∧
        act g.1 g.2 (vec2 k l γ δ) = e12 := by
  decide +kernel

/-- Signed permutations fixing `e₀ - e₁` and `e₁ - e₂`. -/
def cands₃ : List (Equiv.Perm (Fin 6) × (Fin 6 → ℤ)) :=
  (1, fun _ => 1) :: (([3, 4, 5] : List (Fin 6)).flatMap fun m => ([1, -1] : List ℤ).map
    fun β => (Equiv.swap 3 m, fun p => if p = 3 then β else 1))

/-- Kernel check: a root `c` with `(e₀ - e₁, c) = 0` and `(e₁ - e₂, c) = -1` is carried to
`e₂ - e₃` or to `-e₀ - e₁` by a signed permutation fixing `e₀ - e₁` and `e₁ - e₂`. -/
theorem root_to_e23_or_n01 : ∀ k l : Fin 6, k ≠ l → ∀ γ ∈ ([1, -1] : List ℤ), ∀ δ ∈ ([1, -1] : List ℤ),
    dot6 e01 (vec2 k l γ δ) = 0 → dot6 e12 (vec2 k l γ δ) = -1 →
      ∃ g ∈ cands₃, (∀ m, g.2 m * g.2 m = 1) ∧ act g.1 g.2 e01 = e01 ∧
        act g.1 g.2 e12 = e12 ∧
          (act g.1 g.2 (vec2 k l γ δ) = e23 ∨ act g.1 g.2 (vec2 k l γ δ) = n01) := by
  decide +kernel

/-- After signed permutations, the chain is `e₀ - e₁, e₁ - e₂` followed by `e₂ - e₃` or
`-e₀ - e₁`. -/
theorem normalize_chain {u : Fin 5 → V6} {v : Fin 5 → Fin 2 → ℤ} (h : IsEmbedding u v)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    ∃ u' : Fin 5 → V6, IsEmbedding u' v ∧ u' 0 = e01 ∧ u' 1 = e12 ∧
      (u' 2 = e23 ∨ u' 2 = n01) := by
  have hgram (i j : Fin 5) (hi : v i = 0) (hj : v j = 0) (w : Fin 5 → V6)
      (hw : IsEmbedding w v) : dot6 (w i) (w j) = gramT i j := by
    have := hw i j; rwa [hi, hj, bilinA2_zero_left, add_zero] at this
  -- a root of `I₆` is `α eᵢ + β eⱼ` (`root_support`)
  have hroot (a : V6) (ha : dot6 a a = 2) : ∃ i j : Fin 6, i ≠ j ∧
      ∃ α ∈ ([1, -1] : List ℤ), ∃ β ∈ ([1, -1] : List ℤ), a = vec2 i j α β := by
    obtain ⟨i, j, hij, hi, hj, hz⟩ := root_support a (dot6_eq_sum a a ▸ ha)
    refine ⟨i, j, hij, a i, by simpa using hi, a j, by simpa using hj, funext fun m => ?_⟩
    simp only [vec2]
    split_ifs <;> simp_all
  -- first root
  obtain ⟨i, j, hij, α, hα, β, hβ, hu0⟩ :=
    hroot (u 0) (by simpa [gramT] using hgram 0 0 hv0 hv0 u h)
  obtain ⟨hε₁, hact₁⟩ := root_to_e01 i j hij α hα β hβ
  set u₁ : Fin 5 → V6 := fun t => act (σ₁ i j) (ε₁ α β) (u t) with hu₁
  have h₁ : IsEmbedding u₁ v := h.act _ _ hε₁
  have h₁0 : u₁ 0 = e01 := by simp only [hu₁, hu0, hact₁]
  -- second root
  obtain ⟨k, l, hkl, γ, hγ, δ, hδ, hu₁1⟩ :=
    hroot (u₁ 1) (by simpa [gramT] using hgram 1 1 hv1 hv1 u₁ h₁)
  have hp₁ : dot6 e01 (vec2 k l γ δ) = -1 := by
    have := hgram 0 1 hv0 hv1 u₁ h₁
    rw [h₁0, hu₁1] at this; simpa [gramT] using this
  obtain ⟨g, -, hεg, hge01, hgb⟩ := root_to_e12 k l hkl γ hγ δ hδ hp₁
  set u₂ : Fin 5 → V6 := fun t => act g.1 g.2 (u₁ t) with hu₂
  have h₂ : IsEmbedding u₂ v := h₁.act _ _ hεg
  have h₂0 : u₂ 0 = e01 := by simp only [hu₂, h₁0, hge01]
  have h₂1 : u₂ 1 = e12 := by simp only [hu₂, hu₁1, hgb]
  -- third root
  obtain ⟨p, q, hpq, γ', hγ', δ', hδ', hu₂2⟩ :=
    hroot (u₂ 2) (by simpa [gramT] using hgram 2 2 hv2 hv2 u₂ h₂)
  have hp₂ : dot6 e01 (vec2 p q γ' δ') = 0 := by
    have := hgram 0 2 hv0 hv2 u₂ h₂
    rw [h₂0, hu₂2] at this; simpa [gramT] using this
  have hp₃ : dot6 e12 (vec2 p q γ' δ') = -1 := by
    have := hgram 1 2 hv1 hv2 u₂ h₂
    rw [h₂1, hu₂2] at this; simpa [gramT] using this
  obtain ⟨g', -, hεg', hg'e01, hg'e12, hg'c⟩ := root_to_e23_or_n01 p q hpq γ' hγ' δ' hδ' hp₂ hp₃
  refine ⟨fun t => act g'.1 g'.2 (u₂ t), h₂.act _ _ hεg', ?_, ?_, ?_⟩
  · simp only [h₂0, hg'e01]
  · simp only [h₂1, hg'e12]
  · simp only [hu₂2]; exact hg'c

/-! ### The final contradiction -/

/-- The integers of square at most 5. -/
def box5 : List ℤ := [-2, -1, 0, 1, 2]

theorem mem_box5 {z : ℤ} (h : z ^ 2 ≤ 5) : z ∈ box5 := by
  have h1 : -2 ≤ z := by nlinarith
  have h2 : z ≤ 2 := by nlinarith
  interval_cases z <;> simp [box5]

/-- Kernel check: vectors of norm 5 and 3 in `K = I₂ ⊥ A₂`. -/
theorem norm_box : ∀ p ∈ box5, ∀ q ∈ box5, ∀ w₀ ∈ box5, ∀ w₁ ∈ box5,
    (p ^ 2 + q ^ 2 + bilinA2 ![w₀, w₁] ![w₀, w₁] = 5 →
      w₀ = 0 ∧ w₁ = 0 ∧ p ^ 2 + q ^ 2 = 5) ∧
    (p ^ 2 + q ^ 2 + bilinA2 ![w₀, w₁] ![w₀, w₁] = 3 →
      p ^ 2 + q ^ 2 = 1 ∧ bilinA2 ![w₀, w₁] ![w₀, w₁] = 2) := by
  decide +kernel

/-- Kernel check: the pairings of the vectors of `I₂` of norms 5 and 5, and of norms
1 and 5. -/
theorem pair_box : ∀ p ∈ box5, ∀ q ∈ box5, ∀ r ∈ box5, ∀ s ∈ box5,
    (p ^ 2 + q ^ 2 = 5 → r ^ 2 + s ^ 2 = 5 → p * r + q * s ≠ -1 ∧ p * r + q * s ≠ -2) ∧
    (p ^ 2 + q ^ 2 = 1 → r ^ 2 + s ^ 2 = 5 → p * r + q * s ≠ 0 ∧ p * r + q * s ≠ -3) := by
  decide +kernel

/-- Vectors of norm at most 5 in `K = I₂ ⊥ A₂`. -/
theorem norm_K (p q : ℤ) (w : Fin 2 → ℤ) {n : ℤ} (hn : n ≤ 5)
    (h : p ^ 2 + q ^ 2 + bilinA2 w w = n) :
    (n = 5 → w = 0 ∧ p ^ 2 + q ^ 2 = 5) ∧ (n = 3 → p ^ 2 + q ^ 2 = 1 ∧ bilinA2 w w = 2) := by
  have hw := bilinA2_self_ge w
  have hb (z : ℤ) (hz : z ^ 2 ≤ 5) : z ∈ box5 := mem_box5 hz
  have hvec : w = ![w 0, w 1] := by funext k; fin_cases k <;> rfl
  have hbox := norm_box p (hb p (by nlinarith [sq_nonneg q, sq_nonneg (w 0), sq_nonneg (w 1)]))
    q (hb q (by nlinarith [sq_nonneg p, sq_nonneg (w 0), sq_nonneg (w 1)]))
    (w 0) (hb (w 0) (by nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg (w 1)]))
    (w 1) (hb (w 1) (by nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg (w 0)]))
  rw [← hvec] at hbox
  refine ⟨fun h5 => ?_, fun h3 => ?_⟩
  · obtain ⟨h0, h1, hpq⟩ := hbox.1 (h.trans h5)
    exact ⟨by rw [hvec, h0, h1]; funext k; fin_cases k <;> rfl, hpq⟩
  · exact hbox.2 (h.trans h3)

/-- The arithmetic of the normalized case `c = e₂ - e₃`. -/
theorem final_arith (x₀ x₁ x₂ x₃ x₄ x₅ y₀ y₁ y₂ y₃ y₄ y₅ : ℤ) (w z : Fin 2 → ℤ)
    (e₁ : x₀ - x₁ = 1) (e₂ : x₁ - x₂ = 0) (e₃ : x₂ - x₃ = 0)
    (f₁ : y₀ - y₁ = 0) (f₂ : y₁ - y₂ = 1) (f₃ : y₂ - y₃ = 0)
    (nx : x₀ * x₀ + x₁ * x₁ + x₂ * x₂ + x₃ * x₃ + x₄ * x₄ + x₅ * x₅ + bilinA2 w w = 6)
    (ny : y₀ * y₀ + y₁ * y₁ + y₂ * y₂ + y₃ * y₃ + y₄ * y₄ + y₅ * y₅ + bilinA2 z z = 7)
    (pxy : x₀ * y₀ + x₁ * y₁ + x₂ * y₂ + x₃ * y₃ + x₄ * y₄ + x₅ * y₅ + bilinA2 w z = -1) :
    False := by
  obtain rfl : x₁ + 1 = x₀ := by linarith
  obtain rfl : x₁ = x₂ := by linarith
  obtain rfl : x₁ = x₃ := by linarith
  obtain rfl : y₁ = y₀ := by linarith
  obtain rfl : y₂ + 1 = y₁ := by linarith
  obtain rfl : y₂ = y₃ := by linarith
  have hw := bilinA2_self_ge w
  have hz := bilinA2_self_ge z
  -- `x = (t+1, t, t, t) + u` with `t = x₁`, and `y = (s+1, s+1, s, s) + v` with `s = y₂`
  have ht₁ : x₁ ≤ 0 := by nlinarith [sq_nonneg x₄, sq_nonneg x₅]
  have ht₂ : -1 ≤ x₁ := by nlinarith [sq_nonneg x₄, sq_nonneg x₅]
  have hs₁ : y₂ ≤ 0 := by nlinarith [sq_nonneg y₄, sq_nonneg y₅]
  have hs₂ : -1 ≤ y₂ := by nlinarith [sq_nonneg y₄, sq_nonneg y₅]
  have hy : y₄ ^ 2 + y₅ ^ 2 + bilinA2 z z = 5 := by
    interval_cases y₂ <;> nlinarith
  obtain ⟨rfl, hy5⟩ := (norm_K y₄ y₅ z le_rfl hy).1 rfl
  have hr (t : ℤ) (ht : t ^ 2 ≤ 5) : t ∈ box5 := mem_box5 ht
  have hy₄ := hr y₄ (by linarith [sq_nonneg y₅])
  have hy₅ := hr y₅ (by linarith [sq_nonneg y₄])
  simp only [bilinA2_zero_right, add_zero] at pxy
  interval_cases x₁
  · -- `t = -1`: `Q(u) = 3` and `(u, v) = 3s`
    have hx : x₄ ^ 2 + x₅ ^ 2 + bilinA2 w w = 3 := by nlinarith
    obtain ⟨hx1, -⟩ := (norm_K x₄ x₅ w (by norm_num) hx).2 rfl
    have := (pair_box x₄ (hr x₄ (by linarith [sq_nonneg x₅])) x₅
      (hr x₅ (by linarith [sq_nonneg x₄])) y₄ hy₄ y₅ hy₅).2 hx1 hy5
    interval_cases y₂
    · exact this.2 (by linarith)
    · exact this.1 (by linarith)
  · -- `t = 0`: `Q(u) = 5` and `(u, v) = -2 - s`
    have hx : x₄ ^ 2 + x₅ ^ 2 + bilinA2 w w = 5 := by nlinarith
    obtain ⟨rfl, hx5⟩ := (norm_K x₄ x₅ w le_rfl hx).1 rfl
    have := (pair_box x₄ (hr x₄ (by linarith [sq_nonneg x₅])) x₅
      (hr x₅ (by linarith [sq_nonneg x₄])) y₄ hy₄ y₅ hy₅).1 hx5 hy5
    interval_cases y₂
    · exact this.1 (by linarith)
    · exact this.2 (by linarith)

/-- No vectors of `I₆ ⊥ A₂` have Gram matrix `T`. -/
theorem not_isEmbedding (u : Fin 5 → V6) (v : Fin 5 → Fin 2 → ℤ) : ¬ IsEmbedding u v := by
  intro h
  have hT (i j : Fin 5) := h i j
  have r0 := root_split (u 0) (v 0) (by simpa [gramT] using hT 0 0)
  have r1 := root_split (u 1) (v 1) (by simpa [gramT] using hT 1 1)
  have r2 := root_split (u 2) (v 2) (by simpa [gramT] using hT 2 2)
  have h01 := hT 0 1
  have h02 := hT 0 2
  have h12 := hT 1 2
  simp only [gramT, Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h01 h02 h12
  rcases r0 with ⟨hv0, -⟩ | ⟨hu0, ha0⟩ <;> rcases r1 with ⟨hv1, -⟩ | ⟨hu1, ha1⟩
  · -- `a, b ∈ I₆`, so `c ∈ I₆`
    rcases r2 with ⟨hv2, -⟩ | ⟨hu2, -⟩
    · obtain ⟨u', hu', h0, h1, h2⟩ := normalize_chain h hv0 hv1 hv2
      have hx (i j : Fin 5) := hu' i j
      have p03 := hx 0 3; have p13 := hx 1 3; have p23 := hx 2 3
      have p04 := hx 0 4; have p14 := hx 1 4; have p24 := hx 2 4
      have p33 := hx 3 3; have p44 := hx 4 4; have p34 := hx 3 4
      rw [h0, hv0] at p03 p04
      rw [h1, hv1] at p13 p14
      rcases h2 with h2 | h2 <;> rw [h2, hv2] at p23 p24
      · simp [gramT] at p03 p13 p23 p04 p14 p24
        simp only [gramT, dot6, Matrix.of_apply, Matrix.cons_val] at p33 p44 p34
        exact final_arith (u' 3 0) (u' 3 1) (u' 3 2) (u' 3 3) (u' 3 4) (u' 3 5)
          (u' 4 0) (u' 4 1) (u' 4 2) (u' 4 3) (u' 4 4) (u' 4 5) (v 3) (v 4)
          p03 p13 p23 p04 p14 p24 p33 p44 p34
      · simp [gramT] at p03 p23
        omega
    · rw [hu2, hv1] at h12; simp at h12
  · rw [hv0, hu1] at h01; simp at h01
  · rw [hu0, hv1] at h01; simp at h01
  · -- `a, b ∈ A₂`, so `c ∈ A₂`
    rcases r2 with ⟨hv2, -⟩ | ⟨hu2, ha2⟩
    · rw [hu1, hv2] at h12; simp at h12
    · rw [hu0, hu1] at h01; rw [hu0, hu2] at h02; rw [hu1, hu2] at h12
      simp only [dot6_zero_left, zero_add] at h01 h02 h12
      exact not_chain_A2 _ _ _ ha0 ha1 ha2 h01 h02 h12

/-- **Proposition 5.1.** No integer matrix `X` satisfies `Xᵀ G X = T`, where `G` is the Gram
matrix of `I₆ ⊥ A₂` and `T` is the quinary Gram matrix of determinant 117. -/
theorem not_represents (X : Matrix (Fin 6 ⊕ Fin 2) (Fin 5) ℤ) : Xᵀ * gramL * X ≠ gramT :=
  fun hX => not_isEmbedding _ _ (isEmbedding_of_eq hX)

end KimKimOh.Quinary

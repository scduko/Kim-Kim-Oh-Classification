import KimKimOh.Tables.Accept3

/-!
# Certified local tables at 2 (`app:correction-tests`)

As at 3, with the residues `(a mod 8, b mod 4, c mod 8, d mod 4, e mod 4, f mod 8)`: the chunk is
`32 a + 8 b + c < 256` and the local index `32 d + 8 e + f < 128`. A witness encodes `X` (digits
modulo 4) and `Y` (digits modulo 2) with `Xᵀ Y ≡ 1 (mod 2)`, and the orbits run over
`e₃ ↦ ε e₃ + α e₁ + β e₂` with `α, β < 4` and `ε ∈ {1, 7}` (`±1` modulo 8).

Congruences are compared through the coefficients `(a, 2b, c, 2d, 2e, f)` of the norm
polynomial in `ZMod 8` (`npoly`): two symmetric matrices agree modulo 8 on the diagonal and modulo 4
off it exactly when these agree.
-/

namespace KimKimOh.Tables

open Matrix

/-! ### Witnesses -/

def xd2 (w r c : ℕ) : ℕ := (w / 4 ^ (3 * r + c)) % 4
def yd2 (w r c : ℕ) : ℕ := (w / 4 ^ 15 / 2 ^ (3 * r + c)) % 2

def Xw2 (w : ℕ) : Matrix (Fin 5) (Fin 3) ℤ := Matrix.of fun r c => (xd2 w r c : ℤ)
def Yw2 (w : ℕ) : Matrix (Fin 5) (Fin 3) ℤ := Matrix.of fun r c => (yd2 w r c : ℤ)

def gramN2 (J : ℕ → ℕ) (w i k : ℕ) : ℕ :=
  J 0 * xd2 w 0 i * xd2 w 0 k + J 1 * xd2 w 1 i * xd2 w 1 k + J 2 * xd2 w 2 i * xd2 w 2 k +
    J 3 * xd2 w 3 i * xd2 w 3 k + J 4 * xd2 w 4 i * xd2 w 4 k

def dotN2 (w i k : ℕ) : ℕ :=
  xd2 w 0 i * yd2 w 0 k + xd2 w 1 i * yd2 w 1 k + xd2 w 2 i * yd2 w 2 k + xd2 w 3 i * yd2 w 3 k +
    xd2 w 4 i * yd2 w 4 k

def spanOK2 (w : ℕ) : Bool :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)].all fun ik =>
    dotN2 w ik.1 ik.2 % 2 == if ik.1 = ik.2 then 1 else 0

/-! ### Residues and orbits -/

def r8 (z : ℤ) : ℕ := (z % 8).toNat
def r4 (z : ℤ) : ℕ := (z % 4).toNat

def blk2 (a b c : ℕ) : ℕ := 32 * a + 8 * b + c

def actD2 (a b d α β ε : ℕ) : ℕ := (ε * d + α * a + β * b) % 4
def actE2 (b c e α β ε : ℕ) : ℕ := (ε * e + α * b + β * c) % 4
def actF2 (a b c d e f α β ε : ℕ) : ℕ :=
  (ε * ε * f + α * α * a + β * β * c + 2 * α * β * b + 2 * ε * α * d + 2 * ε * β * e) % 8

def orbitBit2 (a b c d e f α β ε : ℕ) : ℕ :=
  1 <<< loc2 (actD2 a b d α β ε) (actE2 b c e α β ε) (actF2 a b c d e f α β ε)

def orbit2 (a b c d e f : ℕ) : ℕ :=
  (List.range 4).foldl (fun acc α => acc ||| (List.range 4).foldl (fun acc β => acc |||
    [1, 7].foldl (fun acc ε => acc ||| orbitBit2 a b c d e f α β ε) 0) 0) 0

def witOrbit2 (J : ℕ → ℕ) (w : ℕ) : ℕ :=
  orbit2 (gramN2 J w 0 0 % 8) (gramN2 J w 0 1 % 4) (gramN2 J w 1 1 % 8) (gramN2 J w 0 2 % 4)
    (gramN2 J w 1 2 % 4) (gramN2 J w 2 2 % 8)

/-- **The kernel check of one chunk at 2.** -/
def accChunkOK2 (J : ℕ → ℕ) (A : BT ℕ) (W : BT (List ℕ)) (blk : ℕ) : Bool :=
  let reps := W.get [] 8 blk
  let cov := reps.foldl (fun acc w => acc ||| witOrbit2 J w) 0
  reps.all (fun w => spanOK2 w &&
      blk2 (gramN2 J w 0 0 % 8) (gramN2 J w 0 1 % 4) (gramN2 J w 1 1 % 8) == blk) &&
    (A.get 0 8 blk &&& cov == A.get 0 8 blk)

/-- The test of a ternary against a table at 2. -/
def accepted2 (A : BT ℕ) (g : Tern) : Bool :=
  (A.get 0 8 (blk2 (r8 g.a) (r4 g.b) (r8 g.c))).testBit (loc2 (r4 g.d) (r4 g.e) (r8 g.f))

/-! ### Soundness -/

theorem mem_orbit2 {a b c d e f l : ℕ} (h : (orbit2 a b c d e f).testBit l = true) :
    ∃ α < 4, ∃ β < 4, ∃ ε ∈ [1, 7],
      loc2 (actD2 a b d α β ε) (actE2 b c e α β ε) (actF2 a b c d e f α β ε) = l := by
  unfold orbit2 at h
  rcases testBit_foldl_or _ l _ 0 h with h0 | ⟨α, hα, h1⟩
  · simp at h0
  rcases testBit_foldl_or _ l _ 0 h1 with h0 | ⟨β, hβ, h2⟩
  · simp at h0
  rcases testBit_foldl_or _ l _ 0 h2 with h0 | ⟨ε, hε, h3⟩
  · simp at h0
  exact ⟨α, List.mem_range.mp hα, β, List.mem_range.mp hβ, ε, hε, eq_of_testBit_one_shiftLeft h3⟩

theorem r8_lt (z : ℤ) : r8 z < 8 := by unfold r8; omega
theorem r4_lt (z : ℤ) : r4 z < 4 := by unfold r4; omega

theorem cast_r8 (z : ℤ) : ((r8 z : ℕ) : ZMod 8) = (z : ZMod 8) := by
  have h : ((r8 z : ℕ) : ℤ) = z % 8 := by unfold r8; omega
  rw [← Int.cast_natCast, h]
  exact_mod_cast ZMod.intCast_mod z 8

/-- Twice a residue modulo 4 is twice the number, modulo 8. -/
theorem two_cast_r4 (z : ℤ) : 2 * ((r4 z : ℕ) : ZMod 8) = 2 * (z : ZMod 8) := by
  have h : ((r4 z : ℕ) : ℤ) = z % 4 := by unfold r4; omega
  rw [← Int.cast_natCast, h]
  have e : 2 * (z % 4) = 2 * z - 8 * (z / 4) := by omega
  have := congrArg (fun t : ℤ => (t : ZMod 8)) e
  push_cast at this
  rw [this, show (8 : ZMod 8) = 0 by decide, zero_mul, sub_zero]

theorem two_cast_mod4 (n : ℕ) : 2 * ((n % 4 : ℕ) : ZMod 8) = 2 * (n : ZMod 8) := by
  have e : 2 * (n % 4) + 8 * (n / 4) = 2 * n := by omega
  have := congrArg (fun t : ℕ => (t : ZMod 8)) e
  push_cast at this
  rw [← this, show (8 : ZMod 8) = 0 by decide, zero_mul, add_zero]

theorem cast_mod8 (n : ℕ) : ((n % 8 : ℕ) : ZMod 8) = (n : ZMod 8) := ZMod.natCast_mod n 8

theorem gram_Xw2 (J : ℕ → ℕ) (w : ℕ) (i k : Fin 3) :
    ((Xw2 w)ᵀ * diagonal (fun r : Fin 5 => (J r : ℤ)) * Xw2 w) i k = (gramN2 J w i k : ℤ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_five,
    Xw2, Matrix.of_apply, gramN2]
  simp
  ring

theorem dot_Xw2 (w : ℕ) (i k : Fin 3) : ((Xw2 w)ᵀ * Yw2 w) i k = (dotN2 w i k : ℤ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five, Xw2, Yw2, Matrix.of_apply,
    dotN2]
  simp

theorem span_of_spanOK2 {w : ℕ} (h : spanOK2 w = true) :
    ∀ i k : Fin 3, (2 : ℤ) ∣ ((Xw2 w)ᵀ * Yw2 w) i k - (1 : Matrix (Fin 3) (Fin 3) ℤ) i k := by
  unfold spanOK2 at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
  intro i k
  rw [dot_Xw2]
  fin_cases i <;> fin_cases k <;> simp at h ⊢ <;> omega

theorem cast_eps2 {ε : ℕ} (hε : ε ∈ [1, 7]) : (ε : ZMod 8) = ((epsOf ε : ℤ) : ZMod 8) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hε
  rcases hε with rfl | rfl
  · simp [epsOf]
  · simp [epsOf]; decide

/-- Agreement of the norm polynomials modulo 8 gives the congruences of
`lem:local-precision` at 2. -/
theorem cong_of_npoly {M C : Matrix (Fin 3) (Fin 3) ℤ} (hM : Mᵀ = M) (hC : Cᵀ = C)
    (h00 : (M 0 0 : ZMod 8) = C 0 0) (h01 : (2 * M 0 1 : ZMod 8) = 2 * C 0 1)
    (h11 : (M 1 1 : ZMod 8) = C 1 1) (h02 : (2 * M 0 2 : ZMod 8) = 2 * C 0 2)
    (h12 : (2 * M 1 2 : ZMod 8) = 2 * C 1 2) (h22 : (M 2 2 : ZMod 8) = C 2 2) :
    (∀ i j, (4 : ℤ) ∣ M i j - C i j) ∧ ∀ i, (8 : ℤ) ∣ M i i - C i i := by
  have d8 : ∀ u v : ℤ, (u : ZMod 8) = v → (8 : ℤ) ∣ u - v := fun u v h => by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub v u 8).mp h.symm; exact_mod_cast this
  have d4 : ∀ u v : ℤ, (2 * u : ZMod 8) = 2 * v → (4 : ℤ) ∣ u - v := fun u v h => by
    have h' : ((2 * u : ℤ) : ZMod 8) = ((2 * v : ℤ) : ZMod 8) := by push_cast; exact h
    have := d8 _ _ h'
    omega
  have e00 := d8 _ _ h00; have e11 := d8 _ _ h11; have e22 := d8 _ _ h22
  have e01 := d4 _ _ h01; have e02 := d4 _ _ h02; have e12 := d4 _ _ h12
  have sM : ∀ i j, M j i = M i j := fun i j => congrFun (congrFun hM i) j
  have sC : ∀ i j, C j i = C i j := fun i j => congrFun (congrFun hC i) j
  have h48 : ∀ x : ℤ, (8 : ℤ) ∣ x → (4 : ℤ) ∣ x := fun x h => dvd_trans (by norm_num) h
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h48 _ e00
    · exact e01
    · exact e02
    · show (4 : ℤ) ∣ M 1 0 - C 1 0; rw [sM 0 1, sC 0 1]; exact e01
    · exact h48 _ e11
    · exact e12
    · show (4 : ℤ) ∣ M 2 0 - C 2 0; rw [sM 0 2, sC 0 2]; exact e02
    · show (4 : ℤ) ∣ M 2 1 - C 2 1; rw [sM 1 2, sC 1 2]; exact e12
    · exact h48 _ e22
  · fin_cases i
    · exact e00
    · exact e11
    · exact e22

/-- The entries of `Pᵀ G P` for `P : e₃ ↦ ε e₃ + α e₁ + β e₂` and `G` symmetric. -/
theorem shear_entries (G : Matrix (Fin 3) (Fin 3) ℤ) (hG : Gᵀ = G) (α β ε : ℤ) :
    ((shearP α β ε)ᵀ * G * shearP α β ε) 0 0 = G 0 0 ∧
    ((shearP α β ε)ᵀ * G * shearP α β ε) 0 1 = G 0 1 ∧
    ((shearP α β ε)ᵀ * G * shearP α β ε) 1 1 = G 1 1 ∧
    ((shearP α β ε)ᵀ * G * shearP α β ε) 0 2 = ε * G 0 2 + α * G 0 0 + β * G 0 1 ∧
    ((shearP α β ε)ᵀ * G * shearP α β ε) 1 2 = ε * G 1 2 + α * G 0 1 + β * G 1 1 ∧
    ((shearP α β ε)ᵀ * G * shearP α β ε) 2 2 = ε * ε * G 2 2 + α * α * G 0 0 + β * β * G 1 1 +
      2 * α * β * G 0 1 + 2 * ε * α * G 0 2 + 2 * ε * β * G 1 2 := by
  have s10 : G 1 0 = G 0 1 := congrFun (congrFun hG 0) 1
  have s20 : G 2 0 = G 0 2 := congrFun (congrFun hG 0) 2
  have s21 : G 2 1 = G 1 2 := congrFun (congrFun hG 1) 2
  simp only [shearP, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  simp [s10, s20, s21]
  refine ⟨by ring, by ring, by ring⟩

open KimKimOh.Local in
/-- **Soundness of a certified table at 2.** -/
theorem sound2 {κ : Type*} [Fintype κ] (K : Matrix κ κ ℤ) (J : ℕ → ℕ)
    (hloc : ∀ X Y : Matrix (Fin 5) (Fin 3) ℤ,
      (∀ i j, (2 : ℤ) ∣ (Xᵀ * Y) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j) →
      ∀ C : Matrix (Fin 3) (Fin 3) ℤ, Cᵀ = C →
      (∀ i j, (4 : ℤ) ∣ (Xᵀ * diagonal (fun r : Fin 5 => (J r : ℤ)) * X) i j - C i j) →
      (∀ i, (8 : ℤ) ∣ (Xᵀ * diagonal (fun r : Fin 5 => (J r : ℤ)) * X) i i - C i i) →
      LocallyRepresents K C 2)
    (A : BT ℕ) (W : BT (List ℕ)) (hA : ∀ blk < 256, accChunkOK2 J A W blk = true)
    (g : Tern) (hg : accepted2 A g = true) : LocallyRepresents K g.toMatrix 2 := by
  have ha8 := r8_lt g.a; have hb4 := r4_lt g.b; have hc8 := r8_lt g.c
  have hd4 := r4_lt g.d; have he4 := r4_lt g.e; have hf8 := r8_lt g.f
  have hblk : blk2 (r8 g.a) (r4 g.b) (r8 g.c) < 256 := by unfold blk2; omega
  have hck := hA _ hblk
  unfold accChunkOK2 at hck
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hck
  obtain ⟨hreps, hcov⟩ := hck
  have hbit := hg
  unfold accepted2 at hbit
  rw [← hcov, Nat.testBit_and, Bool.and_eq_true] at hbit
  rcases testBit_foldl_or _ _ _ 0 hbit.2 with h0 | ⟨w, hw, hwo⟩
  · simp at h0
  obtain ⟨hspan, hwblk⟩ := hreps w hw
  obtain ⟨α, hα, β, hβ, ε, hε, hl⟩ := mem_orbit2 hwo
  set n00 := gramN2 J w 0 0; set n01 := gramN2 J w 0 1; set n11 := gramN2 J w 1 1
  set n02 := gramN2 J w 0 2; set n12 := gramN2 J w 1 2; set n22 := gramN2 J w 2 2
  have h1 : n00 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 : n01 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h3 : n11 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  obtain ⟨ea, eb, ec⟩ : r8 g.a = n00 % 8 ∧ r4 g.b = n01 % 4 ∧ r8 g.c = n11 % 8 := by
    unfold blk2 at hwblk; omega
  have hD := Nat.mod_lt (ε * (n02 % 4) + α * (n00 % 8) + β * (n01 % 4)) (show 0 < 4 by norm_num)
  have hE := Nat.mod_lt (ε * (n12 % 4) + α * (n01 % 4) + β * (n11 % 8)) (show 0 < 4 by norm_num)
  have hF := Nat.mod_lt (ε * ε * (n22 % 8) + α * α * (n00 % 8) + β * β * (n11 % 8) +
    2 * α * β * (n01 % 4) + 2 * ε * α * (n02 % 4) + 2 * ε * β * (n12 % 4)) (show 0 < 8 by norm_num)
  obtain ⟨ed, ee, ef⟩ : actD2 (n00 % 8) (n01 % 4) (n02 % 4) α β ε = r4 g.d ∧
      actE2 (n01 % 4) (n11 % 8) (n12 % 4) α β ε = r4 g.e ∧
      actF2 (n00 % 8) (n01 % 4) (n11 % 8) (n02 % 4) (n12 % 4) (n22 % 8) α β ε = r8 g.f := by
    unfold loc2 at hl; unfold actD2 actE2 actF2 at hl ⊢; omega
  set ε' := epsOf ε
  have hε' : ε' * ε' = 1 := epsOf_sq ε
  set P := shearP α β ε'
  set Q := shearPinv α β ε'
  have hQP : Q * P = 1 := shearPinv_mul hε'
  set JD := diagonal (fun r : Fin 5 => (J r : ℤ))
  set G := (Xw2 w)ᵀ * JD * Xw2 w
  have hGs : Gᵀ = G := by
    simp only [G, JD, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have hB : (Xw2 w * P)ᵀ * JD * (Xw2 w * P) = Pᵀ * G * P := by
    simp only [G]; rw [transpose_mul]; simp only [Matrix.mul_assoc]
  obtain ⟨b00, b01, b11, b02, b12, b22⟩ := shear_entries G hGs α β ε'
  have g00 : G 0 0 = n00 := gram_Xw2 J w 0 0
  have g01 : G 0 1 = n01 := gram_Xw2 J w 0 1
  have g11 : G 1 1 = n11 := gram_Xw2 J w 1 1
  have g02 : G 0 2 = n02 := gram_Xw2 J w 0 2
  have g12 : G 1 2 = n12 := gram_Xw2 J w 1 2
  have g22 : G 2 2 = n22 := gram_Xw2 J w 2 2
  -- the six congruences of the norm polynomials, in `ZMod 8`
  have c00 := cast_mod8 n00; have c11 := cast_mod8 n11; have c22 := cast_mod8 n22
  have c01 := two_cast_mod4 n01; have c02 := two_cast_mod4 n02; have c12 := two_cast_mod4 n12
  have cε := cast_eps2 hε
  have hC : g.toMatrix 0 0 = g.a ∧ g.toMatrix 0 1 = g.b ∧ g.toMatrix 1 1 = g.c ∧
      g.toMatrix 0 2 = g.d ∧ g.toMatrix 1 2 = g.e ∧ g.toMatrix 2 2 = g.f := by
    simp [Tern.toMatrix]
  obtain ⟨t00, t01, t11, t02, t12, t22⟩ := hC
  have key := cong_of_npoly (M := (Xw2 w * P)ᵀ * JD * (Xw2 w * P)) (C := g.toMatrix)
    (by simp only [JD, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc])
    (Tern.toMatrix_transpose g)
    (by rw [hB, b00, g00, t00, ← cast_r8 g.a, ea]; push_cast; rw [c00])
    (by rw [hB, b01, g01, t01, ← two_cast_r4 g.b, eb]; push_cast; rw [c01])
    (by rw [hB, b11, g11, t11, ← cast_r8 g.c, ec]; push_cast; rw [c11])
    (by
      rw [hB, b02, g02, g00, g01, t02, ← two_cast_r4 g.d, ← ed]
      unfold actD2
      rw [two_cast_mod4]; push_cast
      linear_combination (-(↑ε : ZMod 8)) * c02 - 2 * (↑n02 : ZMod 8) * cε -
        2 * (↑α : ZMod 8) * c00 - (↑β : ZMod 8) * c01)
    (by
      rw [hB, b12, g12, g01, g11, t12, ← two_cast_r4 g.e, ← ee]
      unfold actE2
      rw [two_cast_mod4]; push_cast
      linear_combination (-(↑ε : ZMod 8)) * c12 - 2 * (↑n12 : ZMod 8) * cε -
        (↑α : ZMod 8) * c01 - 2 * (↑β : ZMod 8) * c11)
    (by
      rw [hB, b22, g22, g00, g11, g01, g02, g12, t22, ← cast_r8 g.f, ← ef]
      unfold actF2
      rw [cast_mod8]; push_cast
      linear_combination (-(↑ε * ↑ε : ZMod 8)) * c22 - ((↑ε : ZMod 8) + ↑ε') * ↑n22 * cε -
        (↑α * ↑α : ZMod 8) * c00 - (↑β * ↑β : ZMod 8) * c11 - (↑α * ↑β : ZMod 8) * c01 -
        (↑ε * ↑α : ZMod 8) * c02 - 2 * (↑α : ZMod 8) * ↑n02 * cε - (↑ε * ↑β : ZMod 8) * c12 -
        2 * (↑β : ZMod 8) * ↑n12 * cε)
  refine hloc (Xw2 w * P) (Yw2 w * Qᵀ) ?_ g.toMatrix (Tern.toMatrix_transpose g) key.1 key.2
  have e : (Xw2 w * P)ᵀ * (Yw2 w * Qᵀ) - 1 = Pᵀ * ((Xw2 w)ᵀ * Yw2 w - 1) * Qᵀ := by
    have hPQ : Pᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQP, transpose_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, transpose_mul]
    simp only [Matrix.mul_assoc]
  intro i j
  rw [← Matrix.sub_apply, e]
  exact dvd_mul_mul_apply _ _ _ (fun a b => by
    rw [Matrix.sub_apply]; exact span_of_spanOK2 hspan a b) i j

end KimKimOh.Tables

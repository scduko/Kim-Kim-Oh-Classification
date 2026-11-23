import KimKimOh.Tables.Bits
import KimKimOh.Local.Diagonal
import KimKimOh.Ternary
import Mathlib.Data.ZMod.Basic

/-!
# Certified local tables at 3 (`app:correction-tests`)

A table at 3 is a tree `A` of 729-bit chunks, indexed by the leading binary block `(a, b, c)`
modulo 9; bit `81 d + 9 e + f` of chunk `81 a + 9 b + c` marks the residue `(a, b, c, d, e, f)`
(`accepted3`). With it comes a tree `W` of witnesses: a witness `w` encodes integer `5 × 3`
matrices `X` (digits modulo 9) and `Y` (digits modulo 3) with `Xᵀ Y ≡ 1 (mod 3)`.

`accChunkOK3` is the kernel check of one chunk: every witness has `Xᵀ Y ≡ 1`, its Gram residue
`Xᵀ J X` lies in the chunk, and the orbits of the witnessed residues under the changes of basis
`e₃ ↦ ε e₃ + α e₁ + β e₂` (`ε = ±1`), which fix `(a, b, c)`, cover the chunk. For an orbit element
the witness is `X P` with `Y (P⁻¹)ᵀ`.

`sound3`: if every chunk passes, then `lem:local-precision` gives a local representation for every
accepted residue.
-/

namespace KimKimOh.Tables

open Matrix

/-! ### Witnesses -/

/-- The digit of `X` in row `r`, column `c` (base 9). -/
def xd (w r c : ℕ) : ℕ := (w / 9 ^ (3 * r + c)) % 9

/-- The digit of `Y` in row `r`, column `c` (base 3, after the 15 digits of `X`). -/
def yd (w r c : ℕ) : ℕ := (w / 9 ^ 15 / 3 ^ (3 * r + c)) % 3

/-- The integer matrix `X` of a witness. -/
def Xw (w : ℕ) : Matrix (Fin 5) (Fin 3) ℤ := Matrix.of fun r c => (xd w r c : ℤ)

/-- The integer matrix `Y` of a witness. -/
def Yw (w : ℕ) : Matrix (Fin 5) (Fin 3) ℤ := Matrix.of fun r c => (yd w r c : ℤ)

/-- The entry `(i, k)` of `Xᵀ J X` for `J = diag(J 0, …, J 4)`, in naturals. -/
def gramN (J : ℕ → ℕ) (w i k : ℕ) : ℕ :=
  J 0 * xd w 0 i * xd w 0 k + J 1 * xd w 1 i * xd w 1 k + J 2 * xd w 2 i * xd w 2 k +
    J 3 * xd w 3 i * xd w 3 k + J 4 * xd w 4 i * xd w 4 k

/-- The entry `(i, k)` of `Xᵀ Y`, in naturals. -/
def dotN (w i k : ℕ) : ℕ :=
  xd w 0 i * yd w 0 k + xd w 1 i * yd w 1 k + xd w 2 i * yd w 2 k + xd w 3 i * yd w 3 k +
    xd w 4 i * yd w 4 k

/-- `Xᵀ Y ≡ 1 (mod 3)`. -/
def spanOK3 (w : ℕ) : Bool :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)].all fun ik =>
    dotN w ik.1 ik.2 % 3 == if ik.1 = ik.2 then 1 else 0

/-! ### Residues and orbits -/

/-- The residue of an integer modulo 9, in `[0, 9)`. -/
def r9 (z : ℤ) : ℕ := (z % 9).toNat

/-- The chunk index `81 a + 9 b + c`. -/
def blk3 (a b c : ℕ) : ℕ := 81 * a + 9 * b + c

/-- `e₃ ↦ ε e₃ + α e₁ + β e₂` on the last column `(d, e, f)` of a residue, with `ε ∈ {1, 8}`
standing for `±1` modulo 9. -/
def actD (a b d α β ε : ℕ) : ℕ := (ε * d + α * a + β * b) % 9
def actE (b c e α β ε : ℕ) : ℕ := (ε * e + α * b + β * c) % 9
def actF (a b c d e f α β ε : ℕ) : ℕ :=
  (ε * ε * f + α * α * a + β * β * c + 2 * α * β * b + 2 * ε * α * d + 2 * ε * β * e) % 9

/-- The bit of the image of `(d, e, f)` under `(α, β, ε)`. -/
def orbitBit (a b c d e f α β ε : ℕ) : ℕ :=
  1 <<< loc3 (actD a b d α β ε) (actE b c e α β ε) (actF a b c d e f α β ε)

/-- The bits of the orbit of `(d, e, f)` in the chunk `(a, b, c)`. -/
def orbit3 (a b c d e f : ℕ) : ℕ :=
  (List.range 9).foldl (fun acc α => acc ||| (List.range 9).foldl (fun acc β => acc |||
    [1, 8].foldl (fun acc ε => acc ||| orbitBit a b c d e f α β ε) 0) 0) 0

/-- The orbit bits of the residue of a witness. -/
def witOrbit3 (J : ℕ → ℕ) (w : ℕ) : ℕ :=
  orbit3 (gramN J w 0 0 % 9) (gramN J w 0 1 % 9) (gramN J w 1 1 % 9) (gramN J w 0 2 % 9)
    (gramN J w 1 2 % 9) (gramN J w 2 2 % 9)

/-- **The kernel check of one chunk.** -/
def accChunkOK3 (J : ℕ → ℕ) (A : BT ℕ) (W : BT (List ℕ)) (blk : ℕ) : Bool :=
  let reps := W.get [] 10 blk
  let cov := reps.foldl (fun acc w => acc ||| witOrbit3 J w) 0
  reps.all (fun w => spanOK3 w &&
      blk3 (gramN J w 0 0 % 9) (gramN J w 0 1 % 9) (gramN J w 1 1 % 9) == blk) &&
    (A.get 0 10 blk &&& cov == A.get 0 10 blk)

/-- The test of a ternary against a table at 3. -/
def accepted3 (A : BT ℕ) (g : Tern) : Bool :=
  (A.get 0 10 (blk3 (r9 g.a) (r9 g.b) (r9 g.c))).testBit (loc3 (r9 g.d) (r9 g.e) (r9 g.f))

/-! ### Bits of the checks -/

theorem testBit_foldl_or {β : Type*} (f : β → ℕ) (i : ℕ) :
    ∀ (l : List β) (init : ℕ), (l.foldl (fun acc w => acc ||| f w) init).testBit i = true →
      init.testBit i = true ∨ ∃ w ∈ l, (f w).testBit i = true := by
  intro l
  induction l with
  | nil => intro init h; exact Or.inl h
  | cons w l ih =>
    intro init h
    rcases ih _ h with h' | ⟨w', hw', h'⟩
    · rw [Nat.testBit_or, Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨w, by simp, h'⟩
    · exact Or.inr ⟨w', by simp [hw'], h'⟩

theorem testBit_one_shiftLeft {n m : ℕ} : (1 <<< n).testBit m = decide (n = m) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem eq_of_testBit_one_shiftLeft {n i : ℕ} (h : (1 <<< n).testBit i = true) : n = i := by
  rw [testBit_one_shiftLeft] at h
  exact of_decide_eq_true h

/-- A bit of an orbit comes from some `(α, β, ε)`. -/
theorem mem_orbit3 {a b c d e f l : ℕ} (h : (orbit3 a b c d e f).testBit l = true) :
    ∃ α < 9, ∃ β < 9, ∃ ε ∈ [1, 8],
      loc3 (actD a b d α β ε) (actE b c e α β ε) (actF a b c d e f α β ε) = l := by
  unfold orbit3 at h
  rcases testBit_foldl_or _ l _ 0 h with h0 | ⟨α, hα, h1⟩
  · simp at h0
  rcases testBit_foldl_or _ l _ 0 h1 with h0 | ⟨β, hβ, h2⟩
  · simp at h0
  rcases testBit_foldl_or _ l _ 0 h2 with h0 | ⟨ε, hε, h3⟩
  · simp at h0
  exact ⟨α, List.mem_range.mp hα, β, List.mem_range.mp hβ, ε, hε, eq_of_testBit_one_shiftLeft h3⟩

/-! ### The algebra of witnesses -/

theorem r9_lt (z : ℤ) : r9 z < 9 := by unfold r9; omega

theorem cast_r9 (z : ℤ) : ((r9 z : ℕ) : ZMod 9) = (z : ZMod 9) := by
  have h : ((r9 z : ℕ) : ℤ) = z % 9 := by unfold r9; omega
  rw [← Int.cast_natCast, h]
  exact_mod_cast ZMod.intCast_mod z 9

theorem gram_Xw (J : ℕ → ℕ) (w : ℕ) (i k : Fin 3) :
    ((Xw w)ᵀ * diagonal (fun r : Fin 5 => (J r : ℤ)) * Xw w) i k = (gramN J w i k : ℤ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_five,
    Xw, Matrix.of_apply, gramN]
  simp
  ring

theorem dot_Xw (w : ℕ) (i k : Fin 3) : ((Xw w)ᵀ * Yw w) i k = (dotN w i k : ℤ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five, Xw, Yw, Matrix.of_apply,
    dotN]
  simp

theorem span_of_spanOK3 {w : ℕ} (h : spanOK3 w = true) :
    ∀ i k : Fin 3, (3 : ℤ) ∣ ((Xw w)ᵀ * Yw w - (1 : Matrix (Fin 3) (Fin 3) ℤ)) i k := by
  unfold spanOK3 at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
  intro i k
  rw [Matrix.sub_apply, dot_Xw]
  fin_cases i <;> fin_cases k <;> simp at h ⊢ <;> omega

/-- `e₃ ↦ ε e₃ + α e₁ + β e₂`. -/
def shearP (α β ε : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, α; 0, 1, β; 0, 0, ε]

/-- Its inverse when `ε² = 1`. -/
def shearPinv (α β ε : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, -α * ε; 0, 1, -β * ε; 0, 0, ε]

theorem shearPinv_mul {α β ε : ℤ} (hε : ε * ε = 1) : shearPinv α β ε * shearP α β ε = 1 := by
  have h2 : ε ^ 2 = 1 := by rw [sq]; exact hε
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearP, shearPinv, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;> simp [h2]

open KimKimOh.Local KimKimOh.Local.OddPrime in
/-- The change of basis `e₃ ↦ ε e₃ + α e₁ + β e₂` on a ternary over `ZMod 9`. -/
theorem shear_ternMat (α β ε : ℤ) (a b c d e f : ZMod 9) :
    ((shearP α β ε).map (Int.castRingHom (ZMod 9)))ᵀ * ternMat a b c d e f *
        (shearP α β ε).map (Int.castRingHom (ZMod 9)) =
      ternMat a b c (ε * d + α * a + β * b) (ε * e + α * b + β * c)
        (ε * ε * f + α * α * a + β * β * c + 2 * α * β * b + 2 * ε * α * d + 2 * ε * β * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ternMat, shearP, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem cast_mod9 (n : ℕ) : ((n % 9 : ℕ) : ZMod 9) = (n : ZMod 9) := ZMod.natCast_mod n 9

/-- The sign coded by `ε`: `1` for `ε = 1`, else `-1` (the residues `ε ∈ {1, 8}` modulo 9 and
`ε ∈ {1, 7}` modulo 8). -/
def epsOf (ε : ℕ) : ℤ := if ε = 1 then 1 else -1

theorem epsOf_sq (ε : ℕ) : epsOf ε * epsOf ε = 1 := by unfold epsOf; split_ifs <;> norm_num

theorem cast_eps {ε : ℕ} (hε : ε ∈ [1, 8]) : (ε : ZMod 9) = ((epsOf ε : ℤ) : ZMod 9) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hε
  rcases hε with rfl | rfl
  · simp [epsOf]
  · simp [epsOf]; decide

open KimKimOh.Local KimKimOh.Local.OddPrime in
/-- **Soundness of a certified table at 3.** If every chunk passes `accChunkOK3` and
`lem:local-precision` holds for `J`, every accepted ternary is represented by `K` over `ℤ₃`. -/
theorem sound3 {κ : Type*} [Fintype κ] (K : Matrix κ κ ℤ) (J : ℕ → ℕ)
    (hloc : ∀ X Y : Matrix (Fin 5) (Fin 3) ℤ,
      (∀ i j, (3 : ℤ) ∣ (Xᵀ * Y - (1 : Matrix (Fin 3) (Fin 3) ℤ)) i j) →
      ∀ C : Matrix (Fin 3) (Fin 3) ℤ, Cᵀ = C →
      (∀ i j, (9 : ℤ) ∣ (C - Xᵀ * diagonal (fun r : Fin 5 => (J r : ℤ)) * X) i j) →
      LocallyRepresents K C 3)
    (A : BT ℕ) (W : BT (List ℕ)) (hA : ∀ blk < 729, accChunkOK3 J A W blk = true)
    (g : Tern) (hg : accepted3 A g = true) : LocallyRepresents K g.toMatrix 3 := by
  have ha9 := r9_lt g.a; have hb9 := r9_lt g.b; have hc9 := r9_lt g.c
  have hd9 := r9_lt g.d; have he9 := r9_lt g.e; have hf9 := r9_lt g.f
  have hblk : blk3 (r9 g.a) (r9 g.b) (r9 g.c) < 729 := by unfold blk3; omega
  have hck := hA _ hblk
  unfold accChunkOK3 at hck
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hck
  obtain ⟨hreps, hcov⟩ := hck
  have hbit := hg
  unfold accepted3 at hbit
  rw [← hcov, Nat.testBit_and, Bool.and_eq_true] at hbit
  rcases testBit_foldl_or _ _ _ 0 hbit.2 with h0 | ⟨w, hw, hwo⟩
  · simp at h0
  obtain ⟨hspan, hwblk⟩ := hreps w hw
  obtain ⟨α, hα, β, hβ, ε, hε, hl⟩ := mem_orbit3 hwo
  -- the residue of the witness and the residue of `g`
  set ra := gramN J w 0 0 % 9 with hra
  set rb := gramN J w 0 1 % 9 with hrb
  set rc := gramN J w 1 1 % 9 with hrc
  set rd := gramN J w 0 2 % 9 with hrd
  set re := gramN J w 1 2 % 9 with hre
  set rf := gramN J w 2 2 % 9 with hrf
  have hra9 : ra < 9 := Nat.mod_lt _ (by norm_num)
  have hrb9 : rb < 9 := Nat.mod_lt _ (by norm_num)
  have hrc9 : rc < 9 := Nat.mod_lt _ (by norm_num)
  obtain ⟨ea, eb, ec⟩ : r9 g.a = ra ∧ r9 g.b = rb ∧ r9 g.c = rc := by
    unfold blk3 at hwblk; omega
  have hD9 : actD ra rb rd α β ε < 9 := Nat.mod_lt _ (by norm_num)
  have hE9 : actE rb rc re α β ε < 9 := Nat.mod_lt _ (by norm_num)
  have hF9 : actF ra rb rc rd re rf α β ε < 9 := Nat.mod_lt _ (by norm_num)
  obtain ⟨ed, ee, ef⟩ : actD ra rb rd α β ε = r9 g.d ∧ actE rb rc re α β ε = r9 g.e ∧
      actF ra rb rc rd re rf α β ε = r9 g.f := by
    unfold loc3 at hl; omega
  -- the witness `X P`, `Y (P⁻¹)ᵀ`
  set ε' := epsOf ε
  have hε' : ε' * ε' = 1 := epsOf_sq ε
  set P := shearP α β ε'
  set Q := shearPinv α β ε'
  have hQP : Q * P = 1 := shearPinv_mul hε'
  refine hloc (Xw w * P) (Yw w * Qᵀ) ?_ g.toMatrix (Tern.toMatrix_transpose g) ?_
  · have e : (Xw w * P)ᵀ * (Yw w * Qᵀ) - 1 = Pᵀ * ((Xw w)ᵀ * Yw w - 1) * Qᵀ := by
      have hPQ : Pᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQP, transpose_one]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, transpose_mul]
      simp only [Matrix.mul_assoc]
    intro i j
    rw [e]
    exact dvd_mul_mul_apply _ _ _ (span_of_spanOK3 hspan) i j
  · set B := (Xw w * P)ᵀ * diagonal (fun r : Fin 5 => (J r : ℤ)) * (Xw w * P)
    have key : g.toMatrix.map (Int.castRingHom (ZMod 9)) = B.map (Int.castRingHom (ZMod 9)) := by
      -- the left side: the residue of `g`
      rw [Tern.toMatrix_eq_ternMat, map_ternMat]
      simp only [eq_intCast]
      rw [← cast_r9 g.a, ← cast_r9 g.b, ← cast_r9 g.c, ← cast_r9 g.d, ← cast_r9 g.e,
        ← cast_r9 g.f, ea, eb, ec, ← ed, ← ee, ← ef]
      -- the right side: `Pᵀ (Xᵀ J X) P`
      have hgram : ((Xw w)ᵀ * diagonal (fun r : Fin 5 => (J r : ℤ)) * Xw w).map
          (Int.castRingHom (ZMod 9)) = ternMat (ra : ZMod 9) rb rc rd re rf := by
        ext i k
        rw [map_apply, gram_Xw]
        fin_cases i <;> fin_cases k <;> simp [ternMat, hra, hrb, hrc, hrd, hre, hrf, gramN] <;> ring
      have hT : B = Pᵀ * ((Xw w)ᵀ * diagonal (fun r : Fin 5 => (J r : ℤ)) * Xw w) * P := by
        simp only [B]; rw [transpose_mul]; simp only [Matrix.mul_assoc]
      rw [hT, Matrix.map_mul, Matrix.map_mul, transpose_map, hgram, shear_ternMat]
      simp only [actD, actE, actF, cast_mod9]
      push_cast
      rw [cast_eps hε]
    have h := (dvd_sub_iff_map_eq (n := 9) (A := g.toMatrix) (B := B)).mpr key
    intro i j
    rw [Matrix.sub_apply]
    exact_mod_cast h i j

end KimKimOh.Tables

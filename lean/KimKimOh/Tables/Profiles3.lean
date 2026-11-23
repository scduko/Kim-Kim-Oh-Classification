import KimKimOh.Tables.Accept2
import KimKimOh.Correction

/-!
# The sets `𝒰_{j,3}(σ)` and the profiles at 3 (`sec:high`, `app:correction-tests`,
`app:prescriptions`)

For a source residue `σ = (a, b, c, d, e, f)` modulo 9 and `λ̄ = z ∈ 𝔽₃³`, `z ∈ 𝒰_{j,3}(σ)` when
every lift `v` of `z` modulo 9 makes `σ - s vvᵀ` lie in `ℛ_{j,3}`; we then call `z`
*permissible* at `σ`. For the residues of one chunk `(a, b, c)` these form the bitset
`perm3 acc s a b c z`: the intersection over the 27 lifts of translated chunks of the table.

For fixed `x` modulo 3, a *step pair* `(h, d)` says that the pairs `(y, k)` with
`(x, y, k) ∈ 𝒰_{j,3}(σ)` contain a progression: `(1, 1)` all pairs, `(1, 3)` some `k` for every
`y`, `(3, 1)` all `k` for some `y`, `(3, 3)` some pair (`optSet`). A *profile* lists step pairs
for `x = 0, 1, 2`; it holds at `σ` when all of them do (`profSet`).
-/

namespace KimKimOh.Tables

open Matrix

/-- `(u - w) mod 9` for `u < 9`. -/
def sub9 (u w : ℕ) : ℕ := (u + 9 - w % 9) % 9

/-- The chunk of `T - s vvᵀ`. -/
def blkShift3 (s a b c v₀ v₁ : ℕ) : ℕ :=
  blk3 (sub9 a (s * v₀ * v₀)) (sub9 b (s * v₀ * v₁)) (sub9 c (s * v₁ * v₁))

/-- The 27 lifts modulo 9 of `z ∈ 𝔽₃³`. -/
def lifts3 (z₀ z₁ z₂ : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range 3).flatMap fun w₀ => (List.range 3).flatMap fun w₁ => (List.range 3).map fun w₂ =>
    (z₀ + 3 * w₀, z₁ + 3 * w₁, z₂ + 3 * w₂)

/-- All 729 bits. -/
def full729 : ℕ := 2 ^ 729 - 1

/-- The residues of the chunk `(a, b, c)` at which `z` is permissible. -/
def perm3 (acc : BT ℕ) (s a b c z₀ z₁ z₂ : ℕ) : ℕ :=
  (lifts3 z₀ z₁ z₂).foldl (fun m v => m &&& tr3 (acc.get 0 10 (blkShift3 s a b c v.1 v.2.1))
    (s * v.1 * v.2.2) (s * v.2.1 * v.2.2) (s * v.2.2 * v.2.2)) full729

/-! ### Semantics -/

theorem testBit_foldl_and {β : Type*} (F : β → ℕ) (i : ℕ) :
    ∀ (l : List β) (init : ℕ), (l.foldl (fun m w => m &&& F w) init).testBit i = true →
      init.testBit i = true ∧ ∀ w ∈ l, (F w).testBit i = true := by
  intro l
  induction l with
  | nil => intro init h; exact ⟨h, by simp⟩
  | cons w l ih =>
    intro init h
    obtain ⟨h1, h2⟩ := ih _ h
    rw [Nat.testBit_and, Bool.and_eq_true] at h1
    exact ⟨h1.1, fun w' hw' => by
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact h1.2
      · exact h2 w' hw'⟩

/-- `r9 (u - w) = sub9 (r9 u) (r9 w)`. -/
theorem r9_sub (u w : ℤ) : r9 (u - w) = sub9 (r9 u) (r9 w) := by
  unfold r9 sub9; omega

theorem r9_natCast_mul (s : ℕ) (x y : ℤ) : r9 (s * x * y) = (s * r9 x * r9 y) % 9 := by
  have hx : ((r9 x : ℕ) : ℤ) = x % 9 := by unfold r9; omega
  have hy : ((r9 y : ℕ) : ℤ) = y % 9 := by unfold r9; omega
  have hm : (s * (x % 9) * (y % 9)) % 9 = (s * x * y) % 9 :=
    ((Int.mod_modEq x 9).mul_left _).mul (Int.mod_modEq y 9)
  have : ((s * r9 x * r9 y % 9 : ℕ) : ℤ) = (s * x * y) % 9 := by
    push_cast; rw [hx, hy, hm]
  have h2 : ((r9 (s * x * y) : ℕ) : ℤ) = (s * x * y) % 9 := by unfold r9; omega
  exact_mod_cast h2.trans this.symm

/-- The residue of a correction. -/
theorem accepted3_corr (acc : BT ℕ) (g : Tern) (s : ℕ) (x y k : ℤ) :
    accepted3 acc (g.corr s x y k) =
      (acc.get 0 10 (blkShift3 s (r9 g.a) (r9 g.b) (r9 g.c) (r9 x) (r9 y))).testBit
        (loc3 (sub9 (r9 g.d) (s * r9 x * r9 k)) (sub9 (r9 g.e) (s * r9 y * r9 k))
          (sub9 (r9 g.f) (s * r9 k * r9 k))) := by
  unfold accepted3 blkShift3
  simp only [Tern.corr]
  rw [r9_sub, r9_sub, r9_sub, r9_sub, r9_sub, r9_sub, r9_natCast_mul, r9_natCast_mul,
    r9_natCast_mul, r9_natCast_mul, r9_natCast_mul, r9_natCast_mul]
  simp only [sub9, Nat.mod_mod]

/-- The residue of an integer modulo `p`, in `[0, p)`. -/
def rp (p : ℕ) (z : ℤ) : ℕ := (z % (p : ℤ)).toNat

theorem rp_lt {p : ℕ} (hp : 0 < p) (z : ℤ) : rp p z < p := by
  unfold rp
  have h1 := Int.emod_nonneg z (show (p : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos z (show (0 : ℤ) < p by omega)
  omega

theorem rp_eq {p : ℕ} {z : ℤ} {r : ℕ} (h : (p : ℤ) ∣ z - r) (hr : r < p) : rp p z = r := by
  obtain ⟨m, hm⟩ := h
  unfold rp
  have : z % p = r := by
    rw [show z = r + p * m by linarith, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  omega

theorem r9_mod_three (z : ℤ) : r9 z % 3 = rp 3 z := by unfold r9 rp; omega

/-- **A permissible direction.** If bit `(d, e, f)` of `perm3` is set, then every correction of a
ternary with that residue by a `λ` reducing to `z` modulo 3 is accepted. -/
theorem accepted_of_perm3 (acc : BT ℕ) (s : ℕ) (g : Tern) (x y k : ℤ)
    (h : (perm3 acc s (r9 g.a) (r9 g.b) (r9 g.c) (r9 x % 3) (r9 y % 3) (r9 k % 3)).testBit
      (loc3 (r9 g.d) (r9 g.e) (r9 g.f)) = true) :
    accepted3 acc (g.corr s x y k) = true := by
  unfold perm3 at h
  obtain ⟨-, hall⟩ := testBit_foldl_and _ _ _ _ h
  have hmem : (r9 x, r9 y, r9 k) ∈ lifts3 (r9 x % 3) (r9 y % 3) (r9 k % 3) := by
    have hx := r9_lt x; have hy := r9_lt y; have hk := r9_lt k
    simp only [lifts3, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    exact ⟨r9 x / 3, by omega, r9 y / 3, by omega, r9 k / 3, by omega, by omega, by omega,
      by omega⟩
  have := hall _ hmem
  simp only at this
  rw [testBit_tr3 _ _ _ _ (r9_lt _) (r9_lt _) (r9_lt _)] at this
  rw [accepted3_corr]
  unfold sub9
  exact this


theorem corr_neg (g : Tern) (s x y k : ℤ) : g.corr s (-x) (-y) (-k) = g.corr s x y k := by
  unfold Tern.corr; congr 1 <;> ring

/-! ### Step options and profiles, for `p = 2, 3` -/

/-- A step pair `(h, d)` normalized to `(1, 1)`, `(1, p)`, `(p, 1)` or `(p, p)`. -/
def normOpt (p : ℕ) (o : ℕ × ℕ) : ℕ × ℕ :=
  if o.1 == 1 && o.2 == 1 then (1, 1) else if o.1 == 1 then (1, p) else if o.2 == 1 then (p, 1)
  else (p, p)

/-- The residues at which the step pair `o` holds, from the permissible sets `get y k`
(`y, k < p`): `(1, 1)` all pairs, `(1, p)` some `k` for every `y`, `(p, 1)` all `k` for some `y`,
and otherwise some pair. -/
def optSet (p full : ℕ) (get : ℕ → ℕ → ℕ) (o : ℕ × ℕ) : ℕ :=
  if o.1 == 1 && o.2 == 1 then
    (List.range p).foldl (fun m y => m &&& (List.range p).foldl (fun m' k => m' &&& get y k) full)
      full
  else if o.1 == 1 then
    (List.range p).foldl (fun m y => m &&& (List.range p).foldl (fun m' k => m' ||| get y k) 0) full
  else if o.2 == 1 then
    (List.range p).foldl (fun m y => m ||| (List.range p).foldl (fun m' k => m' &&& get y k) full) 0
  else
    (List.range p).foldl (fun m y => m ||| (List.range p).foldl (fun m' k => m' ||| get y k) 0) 0

/-- The residues at which every option of a profile holds (`get x y k`, options for each `x < p`). -/
def profSet (p full : ℕ) (get : ℕ → ℕ → ℕ → ℕ) (P : List (List (ℕ × ℕ))) : ℕ :=
  (List.range p).foldl (fun m x => m &&&
    (P.getD x []).foldl (fun m' o => m' &&& optSet p full (get x) o) full) full

/-- The residues at which some profile of the list holds. -/
def profU (p full : ℕ) (get : ℕ → ℕ → ℕ → ℕ) (profs : List (List (List (ℕ × ℕ)))) : ℕ :=
  profs.foldl (fun u P => u ||| profSet p full get P) 0

/-- A step pair on integers: there is `y₀` such that for every `y ≡ y₀ (mod h)` some class of
`k` modulo `d` satisfies `F y k`. -/
def OptHolds (F : ℤ → ℤ → Prop) (h d : ℕ) : Prop :=
  ∃ y₀ : ℤ, ∀ y : ℤ, (h : ℤ) ∣ y - y₀ → ∃ k₀ : ℤ, ∀ k : ℤ, (d : ℤ) ∣ k - k₀ → F y k

theorem optHolds_of_optSet {p : ℕ} (hp : 0 < p) {full i : ℕ}
    {get : ℕ → ℕ → ℕ} {o : ℕ × ℕ} (h : (optSet p full get o).testBit i = true)
    {F : ℤ → ℤ → Prop} (hF : ∀ y k : ℤ, (get (rp p y) (rp p k)).testBit i = true → F y k) :
    OptHolds F (normOpt p o).1 (normOpt p o).2 := by
  unfold optSet at h
  unfold normOpt
  split_ifs at h ⊢ with h1 h2 h3
  · obtain ⟨-, hall⟩ := testBit_foldl_and
      (fun y => (List.range p).foldl (fun m' k => m' &&& get y k) full) i _ _ h
    refine ⟨0, fun y _ => ⟨0, fun k _ => hF y k ?_⟩⟩
    obtain ⟨-, hk⟩ := testBit_foldl_and (get (rp p y)) i _ _
      (hall _ (List.mem_range.mpr (rp_lt hp y)))
    exact hk _ (List.mem_range.mpr (rp_lt hp k))
  · obtain ⟨-, hall⟩ := testBit_foldl_and
      (fun y => (List.range p).foldl (fun m' k => m' ||| get y k) 0) i _ _ h
    refine ⟨0, fun y _ => ?_⟩
    rcases testBit_foldl_or (get (rp p y)) i _ _ (hall _ (List.mem_range.mpr (rp_lt hp y))) with
      h0 | ⟨k, hk, hbit⟩
    · simp at h0
    refine ⟨k, fun k' hk' => hF y k' ?_⟩
    rwa [rp_eq hk' (List.mem_range.mp hk)]
  · rcases testBit_foldl_or (fun y => (List.range p).foldl (fun m' k => m' &&& get y k) full) i _ _
      h with h0 | ⟨y, hy, hbit⟩
    · simp at h0
    obtain ⟨-, hall⟩ := testBit_foldl_and (get y) i _ _ hbit
    refine ⟨y, fun y' hy' => ⟨0, fun k _ => hF y' k ?_⟩⟩
    rw [rp_eq hy' (List.mem_range.mp hy)]
    exact hall _ (List.mem_range.mpr (rp_lt hp k))
  · rcases testBit_foldl_or (fun y => (List.range p).foldl (fun m' k => m' ||| get y k) 0) i _ _
      h with h0 | ⟨y, hy, hbit⟩
    · simp at h0
    rcases testBit_foldl_or (get y) i _ _ hbit with h0 | ⟨k, hk, hbit'⟩
    · simp at h0
    refine ⟨y, fun y' hy' => ⟨k, fun k' hk' => hF y' k' ?_⟩⟩
    rw [rp_eq hy' (List.mem_range.mp hy), rp_eq hk' (List.mem_range.mp hk)]
    exact hbit'

theorem profSet_spec {p full i : ℕ} {get : ℕ → ℕ → ℕ → ℕ} {P : List (List (ℕ × ℕ))}
    (h : (profSet p full get P).testBit i = true) :
    ∀ x < p, ∀ o ∈ P.getD x [], (optSet p full (get x) o).testBit i = true := by
  intro x hx o ho
  obtain ⟨-, hall⟩ := testBit_foldl_and
    (fun x => (P.getD x []).foldl (fun m' o => m' &&& optSet p full (get x) o) full) i _ _ h
  obtain ⟨-, h2⟩ := testBit_foldl_and (fun o => optSet p full (get x) o) i _ _
    (hall x (List.mem_range.mpr hx))
  exact h2 o ho

theorem profU_spec {p full i : ℕ} {get : ℕ → ℕ → ℕ → ℕ} {profs : List (List (List (ℕ × ℕ)))}
    (h : (profU p full get profs).testBit i = true) :
    ∃ P ∈ profs, (profSet p full get P).testBit i = true := by
  rcases testBit_foldl_or (fun P => profSet p full get P) i _ _ h with h0 | h1
  · simp at h0
  · exact h1

theorem normOpt_two (o : ℕ × ℕ) : (normOpt 2 o).1 ∣ 2 ∧ (normOpt 2 o).2 ∣ 2 := by
  unfold normOpt; split_ifs <;> norm_num

theorem normOpt_three (o : ℕ × ℕ) : (normOpt 3 o).1 ∣ 3 ∧ (normOpt 3 o).2 ∣ 3 := by
  unfold normOpt; split_ifs <;> norm_num

/-- **The Chinese remainder theorem for step pairs** at 2 and 3. -/
theorem optHolds_crt {F₂ F₃ : ℤ → ℤ → Prop} {h₂ d₂ h₃ d₃ : ℕ} (H₂ : OptHolds F₂ h₂ d₂)
    (H₃ : OptHolds F₃ h₃ d₃) (hh₂ : h₂ ∣ 2) (hd₂ : d₂ ∣ 2) (hh₃ : h₃ ∣ 3) (hd₃ : d₃ ∣ 3) :
    OptHolds (fun y k => F₂ y k ∧ F₃ y k) (h₂ * h₃) (d₂ * d₃) := by
  have crt : ∀ {u v : ℕ}, u ∣ 2 → v ∣ 3 → ∀ z z₂ z₃ : ℤ, ((u * v : ℕ) : ℤ) ∣ z - (3 * z₂ - 2 * z₃) →
      (u : ℤ) ∣ z - z₂ ∧ (v : ℤ) ∣ z - z₃ := by
    intro u v hu hv z z₂ z₃ hz
    push_cast at hz
    constructor
    · have : z - z₂ = (z - (3 * z₂ - 2 * z₃)) + 2 * (z₂ - z₃) := by ring
      rw [this]
      exact dvd_add ((Dvd.intro _ rfl).trans hz) (dvd_mul_of_dvd_left (by exact_mod_cast hu) _)
    · have : z - z₃ = (z - (3 * z₂ - 2 * z₃)) + 3 * (z₂ - z₃) := by ring
      rw [this]
      exact dvd_add ((Dvd.intro_left _ rfl).trans hz) (dvd_mul_of_dvd_left (by exact_mod_cast hv) _)
  obtain ⟨y₂, hy₂⟩ := H₂
  obtain ⟨y₃, hy₃⟩ := H₃
  refine ⟨3 * y₂ - 2 * y₃, fun y hy => ?_⟩
  obtain ⟨e₂, e₃⟩ := crt hh₂ hh₃ y y₂ y₃ (by exact_mod_cast hy)
  obtain ⟨k₂, hk₂⟩ := hy₂ y e₂
  obtain ⟨k₃, hk₃⟩ := hy₃ y e₃
  refine ⟨3 * k₂ - 2 * k₃, fun k hk => ?_⟩
  obtain ⟨f₂, f₃⟩ := crt hd₂ hd₃ k k₂ k₃ (by exact_mod_cast hk)
  exact ⟨hk₂ k f₂, hk₃ k f₃⟩

/-! ### The profile check at 3 -/

/-- Representatives of `𝔽₃³` up to sign. -/
def reps3 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2), (1, 0, 0), (1, 0, 1), (1, 0, 2),
    (1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 2, 0), (1, 2, 1), (1, 2, 2)]

/-- The index in `reps3` of `±z`, for `z` at index `9 x + 3 y + k`. -/
def canon3 : List ℕ :=
  [0, 1, 1, 2, 3, 4, 2, 4, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 5, 7, 6, 11, 13, 12, 8, 10, 9]

/-- The permissible sets of a chunk, one for each direction up to sign. -/
def perms3 (acc : BT ℕ) (s a b c : ℕ) : List ℕ :=
  reps3.map fun z => perm3 acc s a b c z.1 z.2.1 z.2.2

/-- The permissible set of the direction `(x, y, k)`. -/
def get3 (ps : List ℕ) (x y k : ℕ) : ℕ := ps.getD (canon3.getD (9 * x + 3 * y + k) 0) 0

/-- `z` is radical modulo 3 with `Q(z) ≡ 0 (mod 9)` (`eq:maximal`). -/
def isoRad3 (a b c d e f z₀ z₁ z₂ : ℕ) : Bool :=
  (a * z₀ + b * z₁ + d * z₂) % 3 == 0 && (b * z₀ + c * z₁ + e * z₂) % 3 == 0 &&
    (d * z₀ + e * z₁ + f * z₂) % 3 == 0 &&
    (a * z₀ * z₀ + c * z₁ * z₁ + f * z₂ * z₂ + 2 * (b * z₀ * z₁ + d * z₀ * z₂ + e * z₁ * z₂)) % 9
      == 0

/-- Nonzero vectors of `𝔽₃³` up to scalars. -/
def zs3 : List (ℕ × ℕ × ℕ) :=
  [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 2, 0), (1, 0, 1), (1, 0, 2), (0, 1, 1),
    (0, 1, 2), (1, 1, 1), (1, 1, 2), (1, 2, 1), (1, 2, 2)]

/-- The residue modulo 9 is not maximal at 3. -/
def nonmax3 (a b c d e f : ℕ) : Bool := zs3.any fun z => isoRad3 a b c d e f z.1 z.2.1 z.2.2

/-- The profiles of a list selected by a bitmask, from index `i`. -/
def maskedAux {α : Type} : List α → ℕ → ℕ → List α
  | [], _, _ => []
  | P :: l, mask, i => if mask.testBit i then P :: maskedAux l mask (i + 1) else maskedAux l mask (i + 1)

/-- The profiles of a list selected by a bitmask. -/
def maskedProfs {α : Type} (profs : List α) (mask : ℕ) : List α := maskedAux profs mask 0

theorem mem_maskedAux {α : Type} {P : α} : ∀ {l : List α} {mask i : ℕ}, P ∈ maskedAux l mask i → P ∈ l
  | [], _, _, h => by simp [maskedAux] at h
  | Q :: l, mask, i, h => by
    unfold maskedAux at h
    split_ifs at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_maskedAux h)
    · exact List.mem_cons_of_mem _ (mem_maskedAux h)

theorem mem_maskedProfs {α : Type} {P : α} {l : List α} {mask : ℕ} (h : P ∈ maskedProfs l mask) :
    P ∈ l := mem_maskedAux h

/-- A 4-bit entry of a table with 64 bits per chunk. -/
def wget (tab blk i : ℕ) : ℕ := (tab >>> (64 * blk + 4 * i)) &&& 15

/-- A 16-bit mask of a table with 16 bits per chunk. -/
def mget (tab blk : ℕ) : ℕ := (tab >>> (16 * blk)) &&& 65535

/-- The residues at which the direction `(x, y)` has `k`-step `w` at 3: all `k` for `w = 1`, some
`k` for `w = 3` (no condition otherwise). -/
def stepSet3 (ps : List ℕ) (x y w : ℕ) : ℕ :=
  if w == 1 then get3 ps x y 0 &&& get3 ps x y 1 &&& get3 ps x y 2
  else if w == 3 then get3 ps x y 0 ||| get3 ps x y 1 ||| get3 ps x y 2
  else full729

/-- **The kernel check of profiles and steps on one chunk at 3**: every maximal residue of the chunk satisfies one of
the profiles selected by the chunk's mask `pm`, and has the `k`-steps of the table `wt` for every
direction `(x, y)` modulo 3. -/
def profChunkOK3 (acc : BT ℕ) (s : ℕ) (profs : ℕ → List (List (List (ℕ × ℕ)))) (pm wt blk : ℕ) :
    Bool :=
  (List.range 729).all fun l =>
    ((List.range 9).foldl (fun m i => m &&& stepSet3 (perms3 acc s (blk / 81) (blk / 9 % 9) (blk % 9))
        (i / 3) (i % 3) (wget wt blk i))
      (profU 3 full729 (get3 (perms3 acc s (blk / 81) (blk / 9 % 9) (blk % 9)))
        (maskedProfs (profs (blk / 81 % 3)) (mget pm blk)))).testBit l ||
    nonmax3 (blk / 81) (blk / 9 % 9) (blk % 9) (l / 81) (l / 9 % 9) (l % 9)

theorem getD_map_of_lt {α β : Type*} (l : List α) (f : α → β) (d : β) (d' : α) {i : ℕ}
    (h : i < l.length) : (l.map f).getD i d = f (l.getD i d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

theorem canon3_spec : ∀ c < 27, canon3.getD c 0 < 14 ∧
    (reps3.getD (canon3.getD c 0) (0, 0, 0) = (c / 9, c / 3 % 3, c % 3) ∨
      reps3.getD (canon3.getD c 0) (0, 0, 0) =
        ((3 - c / 9) % 3, (3 - c / 3 % 3) % 3, (3 - c % 3) % 3)) := by
  decide

theorem get3_perms3 (acc : BT ℕ) (s a b c : ℕ) {x y k : ℕ} (hx : x < 3) (hy : y < 3) (hk : k < 3) :
    get3 (perms3 acc s a b c) x y k = perm3 acc s a b c x y k ∨
      get3 (perms3 acc s a b c) x y k =
        perm3 acc s a b c ((3 - x) % 3) ((3 - y) % 3) ((3 - k) % 3) := by
  obtain ⟨hlt, hz⟩ := canon3_spec (9 * x + 3 * y + k) (by omega)
  have e1 : (9 * x + 3 * y + k) / 9 = x := by omega
  have e2 : (9 * x + 3 * y + k) / 3 % 3 = y := by omega
  have e3 : (9 * x + 3 * y + k) % 3 = k := by omega
  rw [e1, e2, e3] at hz
  have hmap : get3 (perms3 acc s a b c) x y k =
      (fun z : ℕ × ℕ × ℕ => perm3 acc s a b c z.1 z.2.1 z.2.2)
        (reps3.getD (canon3.getD (9 * x + 3 * y + k) 0) (0, 0, 0)) := by
    unfold get3 perms3
    exact getD_map_of_lt _ _ _ _ ((show reps3.length = 14 from rfl) ▸ hlt)
  rcases hz with hz | hz <;> rw [hmap, hz]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem rp_neg_three (z : ℤ) : rp 3 (-z) = (3 - rp 3 z) % 3 := by unfold rp; omega

/-- A set bit of `get3` gives accepted corrections. -/
theorem accepted_of_get3 (acc : BT ℕ) (s : ℕ) (g : Tern) (x y k : ℤ)
    (h : (get3 (perms3 acc s (r9 g.a) (r9 g.b) (r9 g.c)) (rp 3 x) (rp 3 y) (rp 3 k)).testBit
      (loc3 (r9 g.d) (r9 g.e) (r9 g.f)) = true) :
    accepted3 acc (g.corr s x y k) = true := by
  have h3 : (0 : ℕ) < 3 := by norm_num
  rcases get3_perms3 acc s (r9 g.a) (r9 g.b) (r9 g.c) (rp_lt h3 x) (rp_lt h3 y) (rp_lt h3 k) with
    he | he <;> rw [he] at h
  · exact accepted_of_perm3 acc s g x y k (by rwa [r9_mod_three, r9_mod_three, r9_mod_three])
  · rw [← corr_neg]
    exact accepted_of_perm3 acc s g (-x) (-y) (-k) (by
      rwa [r9_mod_three, r9_mod_three, r9_mod_three, rp_neg_three, rp_neg_three, rp_neg_three])

theorem r9_cast (z : ℤ) : ((r9 z : ℕ) : ℤ) = z % 9 := by unfold r9; omega

/-- **A maximal ternary is maximal at 3 residue by residue.** -/
theorem nonmax3_false (g : Tern) (hmax : IsMaximal g.toMatrix) :
    nonmax3 (r9 g.a) (r9 g.b) (r9 g.c) (r9 g.d) (r9 g.e) (r9 g.f) = false := by
  rw [Bool.eq_false_iff]
  intro h
  unfold nonmax3 at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨z₀, z₁, z₂⟩, hz, h⟩ := h
  have ha := r9_cast g.a; have hb := r9_cast g.b; have hc := r9_cast g.c
  have hd := r9_cast g.d; have he := r9_cast g.e; have hf := r9_cast g.f
  simp only [zs3, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hz
  simp only [isoRad3, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine hmax 3 Nat.prime_three ![(z₀ : ℤ), (z₁ : ℤ), (z₂ : ℤ)] ?_ (fun i => ?_) ?_ <;>
  rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals first
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)
    | (fin_cases i <;> simp [Tern.toMatrix, mulVec, dotProduct, Fin.sum_univ_three] <;> omega)
    | (simp [Tern.toMatrix, mulVec, dotProduct, Fin.sum_univ_three]; omega)

/-- The chunk of a ternary at 3. -/
def chunk3 (g : Tern) : ℕ := blk3 (r9 g.a) (r9 g.b) (r9 g.c)

theorem stepSet3_spec {ps : List ℕ} {x y w l : ℕ} (h : (stepSet3 ps x y w).testBit l = true)
    (hw : w = 1 ∨ w = 3) :
    ∃ k₀ < 3, ∀ k < 3, (w = 1 ∨ k = k₀) → (get3 ps x y k).testBit l = true := by
  unfold stepSet3 at h
  rcases hw with rfl | rfl
  · simp only [beq_self_eq_true, ite_true, Nat.testBit_and, Bool.and_eq_true] at h
    exact ⟨0, by norm_num, fun k hk _ => by interval_cases k <;> simp_all⟩
  · simp only [show ((3 : ℕ) == 1) = false from rfl, beq_self_eq_true, ite_true,
      Bool.false_eq_true, ite_false, Nat.testBit_or, Bool.or_eq_true] at h
    have key : ∀ k₀ < 3, (get3 ps x y k₀).testBit l = true →
        ∃ k₀ < 3, ∀ k < 3, (3 = 1 ∨ k = k₀) → (get3 ps x y k).testBit l = true :=
      fun k₀ hk₀ hb => ⟨k₀, hk₀, fun k _ hk' => by
        rcases hk' with h' | rfl
        · exact absurd h' (by norm_num)
        · exact hb⟩
    rcases h with (h | h) | h
    · exact key 0 (by norm_num) h
    · exact key 1 (by norm_num) h
    · exact key 2 (by norm_num) h

/-- **The profiles and the `k`-steps at 3.** If every chunk passes `profChunkOK3`, then every maximal
ternary satisfies a profile selected by the mask of its chunk, and for every direction `(x, y)`
whose table entry `w` is 1 or 3, the corrections are accepted on a class of `k` modulo `w`. -/
theorem chunk3_spec (acc : BT ℕ) (s : ℕ) (profs : ℕ → List (List (List (ℕ × ℕ)))) (pm wt : ℕ)
    (hOK : ∀ blk < 729, profChunkOK3 acc s profs pm wt blk = true) (g : Tern)
    (hmax : IsMaximal g.toMatrix) :
    (∃ P ∈ maskedProfs (profs (rp 3 g.a)) (mget pm (chunk3 g)), ∀ x : ℤ, ∀ o ∈ P.getD (rp 3 x) [],
      OptHolds (fun y k => accepted3 acc (g.corr s x y k) = true) (normOpt 3 o).1
        (normOpt 3 o).2) ∧
    ∀ x y : ℤ, (wget wt (chunk3 g) (3 * rp 3 x + rp 3 y) = 1 ∨
        wget wt (chunk3 g) (3 * rp 3 x + rp 3 y) = 3) →
      ∃ k₀ : ℤ, ∀ k : ℤ, (wget wt (chunk3 g) (3 * rp 3 x + rp 3 y) : ℤ) ∣ k - k₀ →
        accepted3 acc (g.corr s x y k) = true := by
  have ha := r9_lt g.a; have hb := r9_lt g.b; have hc := r9_lt g.c
  have hd := r9_lt g.d; have he := r9_lt g.e; have hf := r9_lt g.f
  set blk := chunk3 g with hblk
  set l := loc3 (r9 g.d) (r9 g.e) (r9 g.f) with hl
  obtain ⟨hblk', e1, e2, e3⟩ : blk < 729 ∧ blk / 81 = r9 g.a ∧ blk / 9 % 9 = r9 g.b ∧
      blk % 9 = r9 g.c := digits9 ha hb hc
  obtain ⟨hl', f1, f2, f3⟩ : l < 729 ∧ l / 81 = r9 g.d ∧ l / 9 % 9 = r9 g.e ∧
      l % 9 = r9 g.f := digits9 hd he hf
  have hc3 := hOK blk hblk'
  unfold profChunkOK3 at hc3
  rw [List.all_eq_true] at hc3
  have hbit := hc3 l (List.mem_range.mpr hl')
  rw [e1, e2, e3, f1, f2, f3, nonmax3_false g hmax, Bool.or_false, r9_mod_three] at hbit
  obtain ⟨hU, hsteps⟩ := testBit_foldl_and _ _ _ _ hbit
  refine ⟨?_, fun x y hw => ?_⟩
  · obtain ⟨P, hP, hPbit⟩ := profU_spec hU
    refine ⟨P, hP, fun x o ho => ?_⟩
    exact optHolds_of_optSet (by norm_num)
      (profSet_spec hPbit (rp 3 x) (rp_lt (by norm_num) x) o ho)
      (fun y k hyk => accepted_of_get3 acc s g x y k hyk)
  · have hx := rp_lt (show 0 < 3 by norm_num) x
    have hy := rp_lt (show 0 < 3 by norm_num) y
    have hi : 3 * rp 3 x + rp 3 y < 9 := by omega
    have hs := hsteps _ (List.mem_range.mpr hi)
    rw [show (3 * rp 3 x + rp 3 y) / 3 = rp 3 x by omega,
      show (3 * rp 3 x + rp 3 y) % 3 = rp 3 y by omega] at hs
    obtain ⟨k₀, hk₀, hk⟩ := stepSet3_spec hs hw
    refine ⟨k₀, fun k hk' => accepted_of_get3 acc s g x y k ?_⟩
    have hkr := rp_lt (show 0 < 3 by norm_num) k
    refine hk _ hkr ?_
    rcases hw with hw | hw
    · exact Or.inl hw
    · right
      rw [hw] at hk'
      exact rp_eq (by exact_mod_cast hk') hk₀

end KimKimOh.Tables

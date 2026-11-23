import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith

/-!
# Bitsets for the local tables (`app:correction-tests`)

The local tables store sets of Gram residues as bitsets. A residue at 3 is a sextuple
`(a, b, c, d, e, f)` modulo 9; it lies in the *chunk* of its leading binary block `(a, b, c)`,
and its *local index* is `81 d + 9 e + f < 729`. At 2 the moduli are `(8, 4, 8, 4, 4, 8)`, the
chunk is `(a, b, c)` and the local index `32 d + 8 e + f < 128`.

* `BT`: a binary tree, the chunks of a table indexed by the chunk number.
* `trBits n m m' k k' = (n ∧ m) <<< k ∨ (n ∧ m') >>> k'`. Its bits are described by
  `testBit_trBits`; when the masks satisfy a finite condition (`ShiftOk`, checked by `decide`),
  bit `i` of the result is bit `σ i` of `n` (`testBit_trBits_of_ok`). With the masks of the
  residues whose digit can grow by `h` without wrapping, this adds `h` to one digit of every
  element (`shiftDigit3`, `shiftDigit2`).
-/

namespace KimKimOh.Tables

/-! ### Trees of chunks -/

/-- A binary tree with leaves in `α`. -/
inductive BT (α : Type)
  | leaf (a : α)
  | node (l r : BT α)

/-- The leaf at index `i` of a tree of depth `k` (bits of `i` from the top), or `dflt`. -/
def BT.get {α : Type} (dflt : α) : BT α → ℕ → ℕ → α
  | .leaf a, _, _ => a
  | .node l r, k + 1, i => if i < 2 ^ k then l.get dflt k i else r.get dflt k (i - 2 ^ k)
  | .node _ _, 0, _ => dflt

/-! ### Shifts of bitsets -/

/-- `(n ∧ m) <<< k ∨ (n ∧ m') >>> k'`. -/
def trBits (n m m' k k' : ℕ) : ℕ := ((n &&& m) <<< k) ||| ((n &&& m') >>> k')

theorem testBit_trBits (n m m' k k' i : ℕ) :
    (trBits n m m' k k').testBit i =
      ((decide (k ≤ i) && (n.testBit (i - k) && m.testBit (i - k))) ||
        (n.testBit (i + k') && m'.testBit (i + k'))) := by
  simp only [trBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, ge_iff_le]
  rw [add_comm k' i]

/-- The finite condition on the masks: below `N`, bit `i` of the shifted set comes from bit `σ i`
of the original set, from the first part when `m` holds at `i - k` and from the second part
otherwise. -/
def ShiftOk (N m m' k k' : ℕ) (σ : ℕ → ℕ) : Prop :=
  ∀ i < N, if k ≤ i ∧ m.testBit (i - k) = true then σ i = i - k ∧ m'.testBit (i + k') = false
    else m'.testBit (i + k') = true ∧ σ i = i + k'

instance (N m m' k k' : ℕ) (σ : ℕ → ℕ) : Decidable (ShiftOk N m m' k k' σ) := by
  unfold ShiftOk; infer_instance

theorem testBit_trBits_of_ok {N m m' k k' : ℕ} {σ : ℕ → ℕ} (h : ShiftOk N m m' k k' σ)
    (n : ℕ) {i : ℕ} (hi : i < N) : (trBits n m m' k k').testBit i = n.testBit (σ i) := by
  have hc := h i hi
  rw [testBit_trBits]
  split_ifs at hc with hk
  · obtain ⟨hσ, hm'⟩ := hc
    rw [hσ, hm', hk.2, decide_eq_true hk.1]
    simp
  · obtain ⟨hm', hσ⟩ := hc
    rw [hσ, hm']
    have : (decide (k ≤ i) && (n.testBit (i - k) && m.testBit (i - k))) = false := by
      by_cases hki : k ≤ i
      · have : m.testBit (i - k) = false := by
          by_contra hne; exact hk ⟨hki, by simpa using hne⟩
        simp [this]
      · simp [hki]
    rw [this]; simp

/-! ### Digit shifts -/

/-- The bits `i < N` satisfying `P`. -/
def maskOf (N : ℕ) (P : ℕ → Bool) : ℕ :=
  (List.range N).foldl (fun acc i => if P i then acc ||| (1 <<< i) else acc) 0

/-- Adding `h` to the digit of stride `st` and radix `r`: the residues with digit below `r - h`
move up by `st h`, the others down by `st (r - h)`. -/
def shiftDigit (N st r h n : ℕ) : ℕ :=
  if h % r = 0 then n else
  trBits n (maskOf N fun i => (i / st) % r < r - h % r) (maskOf N fun i => r - h % r ≤ (i / st) % r)
    (st * (h % r)) (st * (r - h % r))

/-- The index with the digit of stride `st` and radix `r` decreased by `h` modulo `r`. -/
def digitBack (st r h i : ℕ) : ℕ :=
  if h % r = 0 then i else
  if h % r ≤ (i / st) % r then i - st * (h % r) else i + st * (r - h % r)

end KimKimOh.Tables

namespace KimKimOh.Tables

/-- The mask conditions for the digit shifts at 3 (`N = 729`, radix 9, strides 81, 9, 1) and
at 2 (`N = 128`, radices 4, 4, 8, strides 32, 8, 1). -/
theorem shiftOk_three : ∀ st ∈ [81, 9, 1], ∀ h ∈ [1, 2, 3, 4, 5, 6, 7, 8],
    ShiftOk 729 (maskOf 729 fun i => (i / st) % 9 < 9 - h % 9)
      (maskOf 729 fun i => 9 - h % 9 ≤ (i / st) % 9) (st * (h % 9)) (st * (9 - h % 9))
      (digitBack st 9 h) := by
  decide +kernel

theorem shiftOk_two : ∀ sr ∈ [(32, 4), (8, 4), (1, 8)], ∀ h ∈ [1, 2, 3, 4, 5, 6, 7],
    h < sr.2 → ShiftOk 128 (maskOf 128 fun i => (i / sr.1) % sr.2 < sr.2 - h % sr.2)
      (maskOf 128 fun i => sr.2 - h % sr.2 ≤ (i / sr.1) % sr.2) (sr.1 * (h % sr.2))
      (sr.1 * (sr.2 - h % sr.2)) (digitBack sr.1 sr.2 h) := by
  decide +kernel

end KimKimOh.Tables

namespace KimKimOh.Tables

theorem testBit_shiftDigit_three {st : ℕ} (hst : st = 81 ∨ st = 9 ∨ st = 1) (h n : ℕ) {i : ℕ}
    (hi : i < 729) : (shiftDigit 729 st 9 h n).testBit i = n.testBit (digitBack st 9 h i) := by
  unfold shiftDigit
  by_cases h0 : h % 9 = 0
  · simp [h0, digitBack]
  · simp only [h0, ite_false]
    have hmem : h % 9 ∈ [1, 2, 3, 4, 5, 6, 7, 8] := by simp; omega
    have hok := shiftOk_three st (by rcases hst with rfl | rfl | rfl <;> simp) (h % 9) hmem
    simp only [Nat.mod_mod] at hok
    have hdb : digitBack st 9 (h % 9) = digitBack st 9 h := by
      funext j; simp [digitBack]
    rw [hdb] at hok
    exact testBit_trBits_of_ok hok n hi

theorem testBit_shiftDigit_two {st r : ℕ} (hsr : (st, r) = (32, 4) ∨ (st, r) = (8, 4) ∨
    (st, r) = (1, 8)) (h n : ℕ) {i : ℕ} (hi : i < 128) :
    (shiftDigit 128 st r h n).testBit i = n.testBit (digitBack st r h i) := by
  have hr : 0 < r := by rcases hsr with h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  unfold shiftDigit
  by_cases h0 : h % r = 0
  · simp [h0, digitBack]
  · simp only [h0, ite_false]
    have hlt : h % r < r := Nat.mod_lt _ hr
    have hok := shiftOk_two (st, r) (by rcases hsr with h | h | h <;> rw [h] <;> simp) (h % r)
      (by rcases hsr with h' | h' | h' <;> simp only [Prod.mk.injEq] at h' <;> simp <;> omega) hlt
    simp only [Nat.mod_mod] at hok
    have hdb : digitBack st r (h % r) = digitBack st r h := by
      funext j; simp [digitBack]
    rw [hdb] at hok
    exact testBit_trBits_of_ok hok n hi

end KimKimOh.Tables

namespace KimKimOh.Tables

/-- The masks of the digit shifts at 3, as literals (`masks3_eq`). -/
def masks3 : ℕ → ℕ → ℕ × ℕ
  | 81, 1 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1ffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1ffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 3 => (0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 4 => (0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 5 => (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 6 => (0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000)
  | 81, 7 => (0x3ffffffffffffffffffffffffffffffffffffffff, 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000)
  | 81, 8 => (0x1ffffffffffffffffffff, 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000)
  | 9, 1 => (0xffffffffffffffffff007fffffffffffffffff803fffffffffffffffffc01fffffffffffffffffe00ffffffffffffffffff007fffffffffffffffff803fffffffffffffffffc01fffffffffffffffffe00ffffffffffffffffff, 0x1ff000000000000000000ff8000000000000000007fc000000000000000003fe000000000000000001ff000000000000000000ff8000000000000000007fc000000000000000003fe000000000000000001ff000000000000000000)
  | 9, 2 => (0x7fffffffffffffff00003fffffffffffffff80001fffffffffffffffc0000fffffffffffffffe00007fffffffffffffff00003fffffffffffffff80001fffffffffffffffc0000fffffffffffffffe00007fffffffffffffff, 0x1ffff8000000000000000ffffc0000000000000007fffe0000000000000003ffff0000000000000001ffff8000000000000000ffffc0000000000000007fffe0000000000000003ffff0000000000000001ffff8000000000000000)
  | 9, 3 => (0x3fffffffffffff0000001fffffffffffff8000000fffffffffffffc0000007ffffffffffffe0000003fffffffffffff0000001fffffffffffff8000000fffffffffffffc0000007ffffffffffffe0000003fffffffffffff, 0x1ffffffc0000000000000ffffffe00000000000007ffffff00000000000003ffffff80000000000001ffffffc0000000000000ffffffe00000000000007ffffff00000000000003ffffff80000000000001ffffffc0000000000000)
  | 9, 4 => (0x1fffffffffff000000000fffffffffff8000000007ffffffffffc000000003ffffffffffe000000001fffffffffff000000000fffffffffff8000000007ffffffffffc000000003ffffffffffe000000001fffffffffff, 0x1ffffffffe00000000000fffffffff000000000007ffffffff800000000003ffffffffc00000000001ffffffffe00000000000fffffffff000000000007ffffffff800000000003ffffffffc00000000001ffffffffe00000000000)
  | 9, 5 => (0xfffffffff000000000007ffffffff800000000003ffffffffc00000000001ffffffffe00000000000fffffffff000000000007ffffffff800000000003ffffffffc00000000001ffffffffe00000000000fffffffff, 0x1fffffffffff000000000fffffffffff8000000007ffffffffffc000000003ffffffffffe000000001fffffffffff000000000fffffffffff8000000007ffffffffffc000000003ffffffffffe000000001fffffffffff000000000)
  | 9, 6 => (0x7ffffff00000000000003ffffff80000000000001ffffffc0000000000000ffffffe00000000000007ffffff00000000000003ffffff80000000000001ffffffc0000000000000ffffffe00000000000007ffffff, 0x1fffffffffffff8000000fffffffffffffc0000007ffffffffffffe0000003fffffffffffff0000001fffffffffffff8000000fffffffffffffc0000007ffffffffffffe0000003fffffffffffff0000001fffffffffffff8000000)
  | 9, 7 => (0x3ffff0000000000000001ffff8000000000000000ffffc0000000000000007fffe0000000000000003ffff0000000000000001ffff8000000000000000ffffc0000000000000007fffe0000000000000003ffff, 0x1fffffffffffffffc0000fffffffffffffffe00007fffffffffffffff00003fffffffffffffff80001fffffffffffffffc0000fffffffffffffffe00007fffffffffffffff00003fffffffffffffff80001fffffffffffffffc0000)
  | 9, 8 => (0x1ff000000000000000000ff8000000000000000007fc000000000000000003fe000000000000000001ff000000000000000000ff8000000000000000007fc000000000000000003fe000000000000000001ff, 0x1fffffffffffffffffe00ffffffffffffffffff007fffffffffffffffff803fffffffffffffffffc01fffffffffffffffffe00ffffffffffffffffff007fffffffffffffffff803fffffffffffffffffc01fffffffffffffffffe00)
  | 1, 1 => (0xff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff, 0x100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100)
  | 1, 2 => (0x7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f, 0x180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180)
  | 1, 3 => (0x3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f, 0x1c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0)
  | 1, 4 => (0x1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f, 0x1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0)
  | 1, 5 => (0xf0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f, 0x1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0f87c3e1f0)
  | 1, 6 => (0x70381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e070381c0e07, 0x1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8)
  | 1, 7 => (0x30180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c0603, 0x1fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc)
  | 1, 8 => (0x1008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201, 0x1feff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfeff7fbfdfe)
  | st, h => (maskOf 729 fun i => (i / st) % 9 < 9 - h % 9, maskOf 729 fun i => 9 - h % 9 ≤ (i / st) % 9)

/-- The masks of the digit shifts at 2, as literals (`masks2_eq`). -/
def masks2 : ℕ → ℕ → ℕ × ℕ
  | 32, 1 => (0xffffffffffffffffffffffff, 0xffffffff000000000000000000000000)
  | 32, 2 => (0xffffffffffffffff, 0xffffffffffffffff0000000000000000)
  | 32, 3 => (0xffffffff, 0xffffffffffffffffffffffff00000000)
  | 8, 1 => (0xffffff00ffffff00ffffff00ffffff, 0xff000000ff000000ff000000ff000000)
  | 8, 2 => (0xffff0000ffff0000ffff0000ffff, 0xffff0000ffff0000ffff0000ffff0000)
  | 8, 3 => (0xff000000ff000000ff000000ff, 0xffffff00ffffff00ffffff00ffffff00)
  | 1, 1 => (0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f, 0x80808080808080808080808080808080)
  | 1, 2 => (0x3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0)
  | 1, 3 => (0x1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0)
  | 1, 4 => (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0)
  | 1, 5 => (0x7070707070707070707070707070707, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8)
  | 1, 6 => (0x3030303030303030303030303030303, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc)
  | 1, 7 => (0x1010101010101010101010101010101, 0xfefefefefefefefefefefefefefefefe)
  | _, _ => (0, 0)

theorem masks3_eq : ∀ st ∈ [81, 9, 1], ∀ h ∈ [1, 2, 3, 4, 5, 6, 7, 8],
    masks3 st h = (maskOf 729 fun i => (i / st) % 9 < 9 - h % 9,
      maskOf 729 fun i => 9 - h % 9 ≤ (i / st) % 9) := by
  decide +kernel

theorem masks2_eq : ∀ sr ∈ [(32, 4), (8, 4), (1, 8)], ∀ h ∈ [1, 2, 3, 4, 5, 6, 7], h < sr.2 →
    masks2 sr.1 h = (maskOf 128 fun i => (i / sr.1) % sr.2 < sr.2 - h % sr.2,
      maskOf 128 fun i => sr.2 - h % sr.2 ≤ (i / sr.1) % sr.2) := by
  decide +kernel

/-- `shiftDigit` at 3 with the literal masks. -/
def shiftDigit3 (st h n : ℕ) : ℕ :=
  if h % 9 = 0 then n else
  trBits n (masks3 st (h % 9)).1 (masks3 st (h % 9)).2 (st * (h % 9)) (st * (9 - h % 9))

/-- `shiftDigit` at 2 with the literal masks. -/
def shiftDigit2 (st r h n : ℕ) : ℕ :=
  if h % r = 0 then n else
  trBits n (masks2 st (h % r)).1 (masks2 st (h % r)).2 (st * (h % r)) (st * (r - h % r))

theorem shiftDigit3_eq {st : ℕ} (hst : st = 81 ∨ st = 9 ∨ st = 1) (h n : ℕ) :
    shiftDigit3 st h n = shiftDigit 729 st 9 h n := by
  unfold shiftDigit3 shiftDigit
  by_cases h0 : h % 9 = 0
  · simp [h0]
  · simp only [h0, ite_false]
    have hmem : h % 9 ∈ [1, 2, 3, 4, 5, 6, 7, 8] := by simp; omega
    rw [masks3_eq st (by rcases hst with rfl | rfl | rfl <;> simp) (h % 9) hmem]
    simp only [Nat.mod_mod]

theorem shiftDigit2_eq {st r : ℕ} (hsr : (st, r) = (32, 4) ∨ (st, r) = (8, 4) ∨ (st, r) = (1, 8))
    (h n : ℕ) : shiftDigit2 st r h n = shiftDigit 128 st r h n := by
  have hr : 0 < r := by rcases hsr with h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  unfold shiftDigit2 shiftDigit
  by_cases h0 : h % r = 0
  · simp [h0]
  · simp only [h0, ite_false]
    have hlt : h % r < r := Nat.mod_lt _ hr
    rw [masks2_eq (st, r) (by rcases hsr with h | h | h <;> rw [h] <;> simp) (h % r)
      (by rcases hsr with h' | h' | h' <;> simp only [Prod.mk.injEq] at h' <;> simp <;> omega) hlt]
    simp only [Nat.mod_mod]

end KimKimOh.Tables

namespace KimKimOh.Tables

/-! ### Translating a chunk -/

/-- The local index `81 d + 9 e + f` of a residue at 3. -/
def loc3 (d e f : ℕ) : ℕ := 81 * d + 9 * e + f

/-- **Base-9 digits.** `81 u + 9 v + w` with `u, v, w < 9` is below `729` and has the digits
`u, v, w`; this decodes both the chunk `blk3 a b c` of a residue and the local index
`loc3 d e f` in it. -/
theorem digits9 {u v w : ℕ} (hu : u < 9) (hv : v < 9) (hw : w < 9) :
    81 * u + 9 * v + w < 729 ∧ (81 * u + 9 * v + w) / 81 = u ∧ (81 * u + 9 * v + w) / 9 % 9 = v ∧
      (81 * u + 9 * v + w) % 9 = w := by
  omega

/-- The local index `32 d + 8 e + f` of a residue at 2. -/
def loc2 (d e f : ℕ) : ℕ := 32 * d + 8 * e + f

/-- Translate a chunk at 3 by `(hd, he, hf)`: add `hd, he, hf` modulo 9 to the digits. -/
def tr3 (n hd he hf : ℕ) : ℕ :=
  shiftDigit3 81 hd (shiftDigit3 9 he (shiftDigit3 1 hf n))

/-- Translate a chunk at 2 by `(hd, he, hf)`, modulo `(4, 4, 8)`. -/
def tr2 (n hd he hf : ℕ) : ℕ :=
  shiftDigit2 32 4 hd (shiftDigit2 8 4 he (shiftDigit2 1 8 hf n))

theorem testBit_tr3 (n hd he hf : ℕ) {d e f : ℕ} (hd9 : d < 9) (he9 : e < 9) (hf9 : f < 9) :
    (tr3 n hd he hf).testBit (loc3 d e f) =
      n.testBit (loc3 ((d + 9 - hd % 9) % 9) ((e + 9 - he % 9) % 9) ((f + 9 - hf % 9) % 9)) := by
  have hhd := Nat.mod_lt hd (show 0 < 9 by norm_num)
  have hhe := Nat.mod_lt he (show 0 < 9 by norm_num)
  have hhf := Nat.mod_lt hf (show 0 < 9 by norm_num)
  have i1 : digitBack 81 9 hd (loc3 d e f) = loc3 ((d + 9 - hd % 9) % 9) e f := by
    unfold digitBack loc3; split_ifs <;> omega
  have i2 : digitBack 9 9 he (loc3 ((d + 9 - hd % 9) % 9) e f) =
      loc3 ((d + 9 - hd % 9) % 9) ((e + 9 - he % 9) % 9) f := by
    unfold digitBack loc3; split_ifs <;> omega
  have i3 : digitBack 1 9 hf (loc3 ((d + 9 - hd % 9) % 9) ((e + 9 - he % 9) % 9) f) =
      loc3 ((d + 9 - hd % 9) % 9) ((e + 9 - he % 9) % 9) ((f + 9 - hf % 9) % 9) := by
    unfold digitBack loc3; split_ifs <;> omega
  unfold tr3
  rw [shiftDigit3_eq (by simp), shiftDigit3_eq (by simp), shiftDigit3_eq (by simp)]
  rw [testBit_shiftDigit_three (by simp) _ _ (by unfold loc3; omega), i1,
    testBit_shiftDigit_three (by simp) _ _ (by unfold loc3; omega), i2,
    testBit_shiftDigit_three (by simp) _ _ (by unfold loc3; omega), i3]

theorem testBit_tr2 (n hd he hf : ℕ) {d e f : ℕ} (hd4 : d < 4) (he4 : e < 4) (hf8 : f < 8) :
    (tr2 n hd he hf).testBit (loc2 d e f) =
      n.testBit (loc2 ((d + 4 - hd % 4) % 4) ((e + 4 - he % 4) % 4) ((f + 8 - hf % 8) % 8)) := by
  have hhd := Nat.mod_lt hd (show 0 < 4 by norm_num)
  have hhe := Nat.mod_lt he (show 0 < 4 by norm_num)
  have hhf := Nat.mod_lt hf (show 0 < 8 by norm_num)
  have i1 : digitBack 32 4 hd (loc2 d e f) = loc2 ((d + 4 - hd % 4) % 4) e f := by
    unfold digitBack loc2; split_ifs <;> omega
  have i2 : digitBack 8 4 he (loc2 ((d + 4 - hd % 4) % 4) e f) =
      loc2 ((d + 4 - hd % 4) % 4) ((e + 4 - he % 4) % 4) f := by
    unfold digitBack loc2; split_ifs <;> omega
  have i3 : digitBack 1 8 hf (loc2 ((d + 4 - hd % 4) % 4) ((e + 4 - he % 4) % 4) f) =
      loc2 ((d + 4 - hd % 4) % 4) ((e + 4 - he % 4) % 4) ((f + 8 - hf % 8) % 8) := by
    unfold digitBack loc2; split_ifs <;> omega
  unfold tr2
  rw [shiftDigit2_eq (by simp), shiftDigit2_eq (by simp), shiftDigit2_eq (by simp)]
  rw [testBit_shiftDigit_two (by simp) _ _ (by unfold loc2; omega), i1,
    testBit_shiftDigit_two (by simp) _ _ (by unfold loc2; omega), i2,
    testBit_shiftDigit_two (by simp) _ _ (by unfold loc2; omega), i3]

end KimKimOh.Tables

import KimKimOh.Tables.Profiles2
import KimKimOh.Compute.WindowBound
import KimKimOh.Compute.Loops

/-!
# The first-pass test of a block, and its kernel-fast copy (computational definitions)
-/

namespace KimKimOh

open Tables

/-- The directions `(x, |y|, y < 0)` of the first pass: `0 ≤ x ≤ 6`, `|y| ≤ 6`, up to sign, with
no prime `p ≥ 5` dividing both entries; the most useful first. -/
def dirsFP : List (ℕ × ℕ × Bool) :=
  [(0, 1, false), (1, 0, false), (1, 1, true), (1, 1, false), (0, 2, false), (2, 0, false),
    (0, 3, false), (1, 2, true), (1, 2, false), (2, 1, true), (3, 0, false), (2, 1, false),
    (2, 2, true), (2, 2, false), (3, 3, true), (1, 3, true), (3, 1, true), (0, 6, false),
    (3, 3, false), (1, 3, false), (3, 2, true), (2, 3, true), (3, 1, false), (6, 0, false),
    (0, 4, false), (2, 3, false), (3, 2, false), (4, 0, false), (1, 4, true), (1, 4, false),
    (4, 1, true), (4, 1, false), (2, 4, true), (2, 4, false), (4, 2, true), (4, 2, false),
    (3, 4, true), (3, 4, false), (4, 3, true), (4, 3, false), (4, 4, true), (4, 4, false),
    (1, 5, true), (1, 5, false), (5, 1, true), (5, 1, false), (2, 5, true), (2, 5, false),
    (5, 2, true), (5, 2, false), (3, 5, true), (3, 5, false), (5, 3, true), (5, 3, false),
    (4, 5, true), (4, 5, false), (5, 4, true), (5, 4, false), (1, 6, true), (1, 6, false),
    (6, 1, true), (6, 1, false), (2, 6, true), (2, 6, false), (6, 2, true), (6, 2, false),
    (3, 6, true), (3, 6, false), (6, 3, true), (6, 3, false), (4, 6, true), (4, 6, false),
    (6, 4, true), (6, 4, false), (5, 6, true), (5, 6, false), (6, 5, true), (6, 5, false),
    (6, 6, true), (6, 6, false)]

/-- The signed second entry of a direction. -/
def dirY (d : ℕ × ℕ × Bool) : ℤ := if d.2.2 then -(d.2.1 : ℤ) else d.2.1

/-- The second entry modulo `m`. -/
def resY (m : ℕ) (d : ℕ × ℕ × Bool) : ℕ := cond d.2.2 ((m - d.2.1 % m) % m) (d.2.1 % m)

/-- `c x² - 2 b x y + a y²` in `ℕ`. -/
def bfN (a b c : ℕ) (d : ℕ × ℕ × Bool) : ℕ :=
  cond d.2.2 (c * d.1 * d.1 + a * d.2.1 * d.2.1 + 2 * b * d.1 * d.2.1)
    (c * d.1 * d.1 + a * d.2.1 * d.2.1 - 2 * b * d.1 * d.2.1)

/-- The window iteration: from `g`, while `pos` holds, accept if `u g < g`, else move to
`u g + 1` (at most `fuel` times). -/
def winIter (pos : ℕ → Bool) (u : ℕ → ℕ) (fuel : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ r g => pos g && (Nat.blt (u g) g || r (u g + 1))) fuel

/-- The direction data `(x, |y|, y < 0, index at 2, index at 3)`. -/
def dirsD : List (ℕ × ℕ × Bool × ℕ × ℕ) :=
  dirsFP.map fun d => (d.1, d.2.1, d.2.2, 4 * (d.1 % 4) + resY 4 d, 3 * (d.1 % 3) + resY 3 d)

/-- The fast window: with at most one small prime (`gs < 35`) and no weight 2
(`gcd(Δ, δ) < 5`), `G = 1 + [gs > 1] + largeBound (Δ / gs)`; the value 99 marks that the fast
window does not apply. -/
def fastG (Δ δ : ℕ) : ℕ :=
  cond (Nat.blt (Nat.gcd Δ prim47) 35 && Nat.blt (Nat.gcd Δ δ) 5)
    (cond (Nat.beq (Nat.gcd Δ prim47) 1) 1 2 + largeBound (Δ / Nat.gcd Δ prim47)) 99

/-- The window test for `Δ`, the step `m` and the block: the fast window when `G ≤ 5` (then
`⌈G/p⌉ = 1` for every `p ≥ 5`, so `ubound G < G`), or the iteration `G ← ubound G + 1` from
`G = 1` (at most 16 steps), accepted at a fixed point `ubound G < G`. In either case
`s a (m G)² < 3 Δ` (`eq:whole-block`). -/
def winOK (s a m Δ δ cnt : ℕ) : Bool :=
  (Nat.ble (fastG Δ δ) 5 && Nat.blt (s * a * (m * fastG Δ δ) ^ 2) (3 * Δ)) ||
    winIter (fun G => Nat.blt (s * a * (m * G) ^ 2) (3 * Δ)) (fun G => ubound Δ δ cnt G) 16 1

/-- **The test of one direction** for the block `(a, b, c)`, with `δ`, the content `cnt` and the
rows of the step tables for its chunks. The steps `w₂ ∈ {1, 2, 4}` and `w₃ ∈ {1, 3}` are 4-bit
entries; the entry 15 marks a direction without a step, and the test `w₂ w₃ < 13` rejects it. -/
def dirOK (s a b c δ cnt row2 row3 : ℕ) (d : ℕ × ℕ × Bool × ℕ × ℕ) : Bool :=
  Nat.blt ((row2 >>> (4 * d.2.2.2.1) &&& 15) * (row3 >>> (4 * d.2.2.2.2) &&& 15)) 13 &&
  Nat.blt (s * bfN a b c (d.1, d.2.1, d.2.2.1)) δ &&
  winOK s a ((row2 >>> (4 * d.2.2.2.1) &&& 15) * (row3 >>> (4 * d.2.2.2.2) &&& 15))
    (δ - s * bfN a b c (d.1, d.2.1, d.2.2.1)) δ cnt

/-- The row of a step table for a chunk. -/
def rowOf (wt blk : ℕ) : ℕ := (wt >>> (64 * blk)) &&& (2 ^ 64 - 1)

/-- **The first-pass test of a block.** -/
def blockOK (s wt2 wt3 a b c : ℕ) : Bool :=
  anyR dirsD (dirOK s a b c (a * c - b * b) (Nat.gcd a (Nat.gcd b c))
    (rowOf wt2 (blk2 (a % 8) (b % 4) (c % 8))) (rowOf wt3 (blk3 (a % 9) (b % 9) (c % 9))))

/-- The step tables take the values 1, 2, 4 (at 2) and 1, 3 (at 3), or 15 (none). -/
def tableOK2 (wt : ℕ) : Bool :=
  (List.range 256).all fun blk => (List.range 16).all fun i =>
    wget wt blk i == 1 || wget wt blk i == 2 || wget wt blk i == 4 || wget wt blk i == 15

def tableOK3 (wt : ℕ) : Bool :=
  (List.range 729).all fun blk => (List.range 9).all fun i =>
    wget wt blk i == 1 || wget wt blk i == 3 || wget wt blk i == 15

def wtNRaw (δ cnt p : ℕ) : ℕ := cond (Nat.beq (Nat.mod δ p) 0 && !(Nat.beq (Nat.mod cnt p) 0)) 2 1

def smallOfRaw (gs : ℕ) : List ℕ :=
  cond (Nat.beq gs 1) [] (cond (Nat.blt gs 35) [gs]
    (List.rec [] (fun p _ r => cond (Nat.beq (Nat.mod gs p) 0) (p :: r) r) smallPrimes))

def uboundRaw (Δ δ cnt g : ℕ) : ℕ :=
  Nat.add (List.rec 0 (fun p _ r => Nat.add (Nat.mul (wtNRaw δ cnt p) (Nat.div (Nat.sub (Nat.add g p) 1) p)) r)
      (smallOfRaw (Nat.gcd Δ prim47)))
    (Nat.mul (Nat.add (largeBound (Nat.div Δ (Nat.gcd Δ prim47))) (largeBound (Nat.gcd Δ δ)))
      (Nat.div (Nat.add g 52) 53))

def fastGRaw (Δ δ : ℕ) : ℕ :=
  cond (Nat.blt (Nat.gcd Δ prim47) 35 && Nat.blt (Nat.gcd Δ δ) 5)
    (Nat.add (cond (Nat.beq (Nat.gcd Δ prim47) 1) 1 2) (largeBound (Nat.div Δ (Nat.gcd Δ prim47)))) 99

def bfNRaw (a b c : ℕ) (d : ℕ × ℕ × Bool) : ℕ :=
  cond d.2.2
    (Nat.add (Nat.add (Nat.mul (Nat.mul c d.1) d.1) (Nat.mul (Nat.mul a d.2.1) d.2.1))
      (Nat.mul (Nat.mul (Nat.mul 2 b) d.1) d.2.1))
    (Nat.sub (Nat.add (Nat.mul (Nat.mul c d.1) d.1) (Nat.mul (Nat.mul a d.2.1) d.2.1))
      (Nat.mul (Nat.mul (Nat.mul 2 b) d.1) d.2.1))

def winOKRaw (s a m Δ δ cnt : ℕ) : Bool :=
  (Nat.ble (fastGRaw Δ δ) 5 &&
      Nat.blt (Nat.mul (Nat.mul s a) (Nat.pow (Nat.mul m (fastGRaw Δ δ)) 2)) (Nat.mul 3 Δ)) ||
    winIter (fun G => Nat.blt (Nat.mul (Nat.mul s a) (Nat.pow (Nat.mul m G) 2)) (Nat.mul 3 Δ))
      (fun G => uboundRaw Δ δ cnt G) 16 1

def dirOKRaw (s a b c δ cnt row2 row3 : ℕ) (d : ℕ × ℕ × Bool × ℕ × ℕ) : Bool :=
  Nat.blt (Nat.mul (Nat.land (Nat.shiftRight row2 (Nat.mul 4 d.2.2.2.1)) 15)
    (Nat.land (Nat.shiftRight row3 (Nat.mul 4 d.2.2.2.2)) 15)) 13 &&
  Nat.blt (Nat.mul s (bfNRaw a b c (d.1, d.2.1, d.2.2.1))) δ &&
  winOKRaw s a (Nat.mul (Nat.land (Nat.shiftRight row2 (Nat.mul 4 d.2.2.2.1)) 15)
      (Nat.land (Nat.shiftRight row3 (Nat.mul 4 d.2.2.2.2)) 15))
    (Nat.sub δ (Nat.mul s (bfNRaw a b c (d.1, d.2.1, d.2.2.1)))) δ cnt

def rowOfRaw (wt blk : ℕ) : ℕ := Nat.land (Nat.shiftRight wt (Nat.mul 64 blk)) 18446744073709551615

/-- **The kernel-fast first-pass test of a block.** -/
def blockOKRaw (s wt2 wt3 a b c : ℕ) : Bool :=
  anyR dirsD (dirOKRaw s a b c (Nat.sub (Nat.mul a c) (Nat.mul b b)) (Nat.gcd a (Nat.gcd b c))
    (rowOfRaw wt2 (Nat.add (Nat.add (Nat.mul 32 (Nat.mod a 8)) (Nat.mul 8 (Nat.mod b 4))) (Nat.mod c 8)))
    (rowOfRaw wt3 (Nat.add (Nat.add (Nat.mul 81 (Nat.mod a 9)) (Nat.mul 9 (Nat.mod b 9))) (Nat.mod c 9))))

theorem blockOKRaw_eq (s wt2 wt3 a b c : ℕ) : blockOKRaw s wt2 wt3 a b c = blockOK s wt2 wt3 a b c :=
  rfl

end KimKimOh

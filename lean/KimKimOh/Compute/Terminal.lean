import KimKimOh.Compute.Enum

/-!
# The last-column test and the terminal enumeration of `sec:finite` (computational definitions)

For a block `B = (a, b, c)` left by the whole-block test, the completions are grouped into
last-column classes `(ρ₂, κ)`: `ρ₂ = loc2 (d mod 4, e mod 4, f mod 8)` at 2 and `κ = 9 (d mod 3) +
3 (e mod 3) + (f mod 3)` at 3. A set of classes is a number with bit `128 κ + ρ₂` per class. The
classes of maximal completions lie in the *domain*: `4 ∤ D` at 2 (table `r2`), and a lift modulo 9
maximal at 3 (table `mx`).

An *option* (`TermOpt`) is a pair `α = (x, ±y)` with a window `g` and a list `F` of factor entries
(`FactorEntry`) whose product of powers, with 2 and 3, is `Δ` (`stripL`): kept primes, at which `B`
and `α` do not both vanish, and omitted moduli, at which a diagonal entry of `B'` is in the square
class of `j` (`optOK`). For a threshold `T` an option covers
the classes with steps `w₂ ∈ {1, 2, 4}`, `w₃ ∈ {1, 3}` and `s (w₂ w₃ g)² δ² < 4 Δ T`
(`optCover`); at 3 the step is 1 if every maximal lift accepts every `k`, and 3 if every maximal
lift accepts a common `k`.

`termOK` checks the options, computes the classes not covered below `D₀ = ⌈3δ²/(4a)⌉`, checks
that they are covered at `U + 1`, enumerates the maximal lifts in those classes with `D ≤ U`
(`liftsOf`), and checks a witness for each (`witOK`): a covector `λ` with `C = G - s λλᵀ` positive,
accepted at 2 and 3 (possibly through an index-`p` overlattice), and with square-class
certificates at the primes `p ≥ 5` dividing every 2×2 minor of `C`.
-/

namespace KimKimOh

open Tables

/-! ### Bits and loops -/

/-- An entry of a table with `w` bits per chunk. -/
def tget (tab w blk : ℕ) : ℕ := (tab >>> (w * blk)) &&& (2 ^ w - 1)

/-- The classes `(ρ₂, κ)` with `ρ₂ ∈ rows` and `κ ∈ cols`. -/
def pairProd (rows cols : ℕ) : ℕ :=
  natFoldOr 27 fun κ => cond (cols.testBit κ) ((rows &&& full128) <<< (128 * κ)) 0

/-! ### The domain -/

/-- The residues modulo 9 lifting the column class `κ`. -/
def liftMask3 (κ : ℕ) : ℕ :=
  natFoldOr 27 fun w =>
    1 <<< loc3 (κ / 9 + 3 * (w / 9)) (κ / 3 % 3 + 3 * (w / 3 % 3)) (κ % 3 + 3 * (w % 3))

/-- The column classes all of whose lifts in `maxm` lie in `set`. -/
def colsIn (maxm set : ℕ) : ℕ :=
  natFoldOr 27 fun κ =>
    cond (Nat.beq (liftMask3 κ &&& maxm &&& set) (liftMask3 κ &&& maxm)) (1 <<< κ) 0

/-- The column classes with a lift in `maxm`. -/
def colsMax (maxm : ℕ) : ℕ :=
  natFoldOr 27 fun κ => cond (Nat.beq (liftMask3 κ &&& maxm) 0) 0 (1 <<< κ)

/-- The residues of a chunk at 2 with `4 ∤ D`. -/
def rows2 (blk : ℕ) : ℕ :=
  natFoldOr 128 fun l =>
    cond (Nat.beq (det4 (blk / 32) (blk / 8 % 4) (blk % 8) (l / 32) (l / 8 % 4) (l % 8)) 0) 0
      (1 <<< l)

/-- The table `r2` of `rows2` (128 bits per chunk). -/
def r2OK (r2 : ℕ) : Bool := natAllR 256 fun blk => Nat.beq (tget r2 128 blk) (rows2 blk)

/-- The codes `9 z₀ + 3 z₁ + z₂` of `zs3`. -/
def zsMask : ℕ := 261690

/-- The rows of the table `mx` of maximal residues at 3 (729 bits per chunk), with witnesses
`mw` (5 bits per residue): a residue not marked has a radical isotropic vector `z`. -/
def mxRowOK (mxr mwr blk : ℕ) : Bool :=
  natAllR 729 fun l => mxr.testBit l ||
    (zsMask.testBit (tget mwr 5 l) &&
      isoRad3 (blk / 81) (blk / 9 % 9) (blk % 9) (l / 81) (l / 9 % 9) (l % 9)
        (tget mwr 5 l / 9) (tget mwr 5 l / 3 % 3) (tget mwr 5 l % 3))

/-- The rows `lo, …, lo + n - 1` of the tables `mx, mw`. -/
def mxRange (mx mw lo n : ℕ) : Bool :=
  natAllR n fun i => mxRowOK (tget mx 729 (lo + i)) (tget mw 3645 (lo + i)) (lo + i)

/-- The domain of a block. -/
def domainB (r2 maxm a b c : ℕ) : ℕ :=
  pairProd (tget r2 128 (blk2 (a % 8) (b % 4) (c % 8))) (colsMax maxm)

/-! ### Options -/

/-- An entry of the factorization of `Δ` in an option. With `kind = 0`, `q` is a kept prime,
proved prime by trial division below `w + 2`. With `kind = 1` or `2`, the primes of `q` are
omitted, since the diagonal entry `a - s x²` (`kind = 1`) or `c - s y²` (`kind = 2`) of `B'` is
`j w²` modulo `q` with `gcd (w, q) = 1`. -/
structure FactorEntry where
  q : ℕ
  kind : ℕ
  w : ℕ

/-- An option of the last-column test: the pair `α = (x, ±y)` (the sign is negative when
`yneg`), the window `g`, and the factorization `F` of `Δ` into 2, 3 and the entries. -/
structure TermOpt where
  x : ℕ
  y : ℕ
  yneg : Bool
  g : ℕ
  F : List FactorEntry

/-- `|b - s x y|` for the signed `y`. -/
def bAbs (s b x y : ℕ) (yneg : Bool) : ℕ :=
  cond yneg (b + s * x * y) (cond (Nat.ble (s * x * y) b) (b - s * x * y) (s * x * y - b))

/-- `Δ = (a - s x²)(c - s y²) - (b - s x y)²`. -/
def deltaO (s a b c x y : ℕ) (yneg : Bool) : ℕ :=
  (a - s * x * x) * (c - s * y * y) - bAbs s b x y yneg * bAbs s b x y yneg

/-- Remove the factors `p` from `m`, at most `k` times. -/
def stripF (p k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun m => m)
    (fun _ r m => cond (Nat.beq (m % p) 0) (r (m / p)) m) k

/-- Remove the factors `p` from `n` (at most 64 times). -/
def stripP (p n : ℕ) : ℕ := stripF p 64 n

/-- Remove the factors 2, 3 and the moduli `q e` of the entries `e` of `F`. -/
def stripL {α : Type} (q : α → ℕ) (F : List α) (n : ℕ) : ℕ :=
  List.rec (stripP 3 (stripP 2 n)) (fun e _ r => stripP (q e) r) F

/-- `p` is prime: no divisor `2 ≤ m < r + 2`, and `p < (r + 2)²`. -/
def isPrimeTD (p r : ℕ) : Bool :=
  Nat.blt 1 p && Nat.blt p ((r + 2) * (r + 2)) && natAllR r fun i => !(Nat.beq (p % (i + 2)) 0)

/-- The diagonal entry `a - s x²` (`kind = 1`) or `c - s y²` of `B'`. -/
def diagO (s a c x y kind : ℕ) : ℕ := cond (Nat.beq kind 1) (a - s * x * x) (c - s * y * y)

/-- The check of an entry of `F`: a kept prime at which `B` and `α` do not both vanish, or an
omitted modulus with its square root. -/
def entryOK (j s a b c x y : ℕ) (e : FactorEntry) : Bool :=
  cond (Nat.beq e.kind 0)
    (isPrimeTD e.q e.w && !(Nat.beq (a % e.q) 0 && Nat.beq (b % e.q) 0 && Nat.beq (c % e.q) 0 &&
      Nat.beq (x % e.q) 0 && Nat.beq (y % e.q) 0))
    (Nat.beq (Nat.gcd e.w e.q) 1 &&
      Nat.beq (diagO s a c x y e.kind % e.q) (j * e.w * e.w % e.q))

/-- `Σ ν_q ⌈g / q⌉` over the kept entries. -/
def keptSum (δ cnt g : ℕ) (F : List FactorEntry) : ℕ :=
  List.rec 0 (fun e _ r => cond (Nat.beq e.kind 0) (wtN δ cnt e.q * ((g + e.q - 1) / e.q)) 0 + r) F

/-- **The checks of an option** for the block `(a, b, c)`: `B' > 0`, the factorization of `Δ`, its
entries, and the sum inequality of `eq:whole-block` for the window `g`. -/
def optOK (j s a b c : ℕ) (o : TermOpt) : Bool :=
  Nat.blt (s * o.x * o.x) a && Nat.blt (s * o.y * o.y) c &&
  Nat.blt (bAbs s b o.x o.y o.yneg * bAbs s b o.x o.y o.yneg)
    ((a - s * o.x * o.x) * (c - s * o.y * o.y)) &&
  Nat.beq (stripL FactorEntry.q o.F (deltaO s a b c o.x o.y o.yneg)) 1 &&
  allR o.F (entryOK j s a b c o.x o.y) &&
  Nat.ble 1 o.g &&
  Nat.blt (keptSum (a * c - b * b) (Nat.gcd a (Nat.gcd b c)) o.g o.F) o.g

/-! ### Coverage -/

/-- `s (m g)² δ² < 4 Δ T`. -/
def levelOK (s δ Δ T m g : ℕ) : Bool := Nat.blt (s * (m * g) * (m * g) * (δ * δ)) (4 * Δ * T)

/-- The column classes of step 1 at 3. -/
def cols1 (ps : List ℕ) (maxm x y : ℕ) : ℕ :=
  colsIn maxm (get3 ps x y 0 &&& get3 ps x y 1 &&& get3 ps x y 2)

/-- The column classes of step 3 at 3. -/
def cols3 (ps : List ℕ) (maxm x y : ℕ) : ℕ :=
  colsIn maxm (get3 ps x y 0) ||| colsIn maxm (get3 ps x y 1) ||| colsIn maxm (get3 ps x y 2)

/-- The classes covered, from the rows of steps 1, 2, 4 and the columns of steps 1, 3. -/
def coverW (row1 row2 row4 col1 col3 : ℕ) (lv : ℕ → Bool) : ℕ :=
  cond (lv 1) (pairProd row1 col1) 0 ||| cond (lv 2) (pairProd row2 col1) 0 |||
    cond (lv 4) (pairProd row4 col1) 0 ||| cond (lv 3) (pairProd row1 col3) 0 |||
    cond (lv 6) (pairProd row2 col3) 0 ||| cond (lv 12) (pairProd row4 col3) 0

/-- **The classes covered by an option** at the threshold `T`. -/
def optCover (acc2 acc3 : BT ℕ) (s a b c maxm T : ℕ) (o : TermOpt) : ℕ :=
  coverW
    (stepSet2 acc2 s (a % 8) (b % 4) (c % 8) (o.x % 4) (resY 4 (o.x, o.y, o.yneg)) 1)
    (stepSet2 acc2 s (a % 8) (b % 4) (c % 8) (o.x % 4) (resY 4 (o.x, o.y, o.yneg)) 2)
    (stepSet2 acc2 s (a % 8) (b % 4) (c % 8) (o.x % 4) (resY 4 (o.x, o.y, o.yneg)) 4)
    (cols1 (perms3 acc3 s (a % 9) (b % 9) (c % 9)) maxm (o.x % 3) (resY 3 (o.x, o.y, o.yneg)))
    (cols3 (perms3 acc3 s (a % 9) (b % 9) (c % 9)) maxm (o.x % 3) (resY 3 (o.x, o.y, o.yneg)))
    (fun m => levelOK s (a * c - b * b) (deltaO s a b c o.x o.y o.yneg) T m o.g)

/-- The classes covered by some option. -/
def coverAll (acc2 acc3 : BT ℕ) (s a b c maxm T : ℕ) (opts : List TermOpt) : ℕ :=
  List.rec 0 (fun o _ r => optCover acc2 acc3 s a b c maxm T o ||| r) opts

/-! ### The terminal enumeration -/

/-- `⌈n / m⌉`. -/
def cdivZ (n : ℤ) (m : ℕ) : ℤ := -((-n) / (m : ℤ))

/-- The least `e` allowed by size reduction, `2 (a e - b d) ≥ -δ`. -/
def eSize (a b c d : ℕ) : ℤ := cdivZ ((2 * b * d : ℕ) - (a * c - b * b : ℕ)) (2 * a)

/-- The least `e` for `d` after the sign of `e₃`: `e ≥ 0` if `d = 0`. -/
def eSign (a b c d : ℕ) : ℤ := cond (Nat.beq d 0) (max (eSize a b c d) 0) (eSize a b c d)

/-- The least `e` enumerated for `d`: size reduction and the sign normalization, with
`a e ≥ b d` if `b = 0` or `2 b = a`. -/
def eLo (a b c d : ℕ) : ℤ :=
  cond (Nat.beq b 0 || Nat.beq (2 * b) a) (max (eSign a b c d) (cdivZ (b * d : ℕ) a)) (eSign a b c d)

/-- The largest `e` enumerated for `d`. -/
def eHi (a b c d : ℕ) : ℤ := ((2 * b * d + (a * c - b * b) : ℕ) : ℤ) / ((2 * a : ℕ) : ℤ)

/-- `R = c d² - 2 b d e + a e²`. -/
def rDE (a b c d : ℕ) (e : ℤ) : ℕ :=
  ((c * d * d : ℕ) - 2 * (b * d : ℕ) * e + (a : ℤ) * e * e).toNat

/-- `D₀ = ⌈3δ²/(4a)⌉`, the least `D` allowed by reduction (`eq:lengths`). -/
def dZero (a b c : ℕ) : ℕ := (3 * (a * c - b * b) * (a * c - b * b) + 4 * a - 1) / (4 * a)

/-- The least `f`: `f ≥ a`, `a f - d² ≥ δ` and `D ≥ D₀`. -/
def fLo (a b c d : ℕ) (e : ℤ) : ℕ :=
  max a (max ((a * c - b * b + d * d + a - 1) / a)
    ((dZero a b c + rDE a b c d e + (a * c - b * b) - 1) / (a * c - b * b)))

/-- The largest `f`: `D ≤ U`. -/
def fHi (a b c d U : ℕ) (e : ℤ) : ℕ := (U + rDE a b c d e) / (a * c - b * b)

/-- The point `(d, e, f)`: its class is pending, it is maximal at 3 and primitive. -/
def ptOK (a b c d : ℕ) (e : ℤ) (f pend maxm : ℕ) : Bool :=
  pend.testBit (128 * (9 * (d % 3) + 3 * rp 3 e + f % 3) + loc2 (d % 4) (r4 e) (f % 8)) &&
  maxm.testBit (loc3 (d % 9) (r9 e) (f % 9)) &&
  Nat.beq (Nat.gcd a (Nat.gcd b (Nat.gcd c (Nat.gcd d (Nat.gcd e.natAbs f))))) 1

/-- **The enumerated last columns** with `D ≤ U` in the pending classes. -/
def liftsOf (a b c U pend maxm : ℕ) : List (ℕ × ℤ × ℕ) :=
  natFlat (a / 2 + 1) fun d =>
    natFlat (eHi a b c d - eLo a b c d + 1).toNat fun i =>
      natFlat (fHi a b c d U (eLo a b c d + i) + 1 - fLo a b c d (eLo a b c d + i)) fun k =>
        cond (ptOK a b c d (eLo a b c d + i) (fLo a b c d (eLo a b c d + i) + k) pend maxm)
          [(d, eLo a b c d + i, fLo a b c d (eLo a b c d + i) + k)] []

/-! ### Witnesses -/

/-- A square-class certificate: the diagonal entry `i` (`a`, `c`, `f` for `i = 0, 1, 2`) of `C`
is `j w²` modulo `q`, with `gcd (w, q) = 1`. -/
structure SquareCert where
  q : ℕ
  i : ℕ
  w : ℕ

/-- A witness: the covector `λ = (l₀, l₁, l₂)`, the overlattice codes `e₂`, `e₃` at 2 and 3
(`locOK`), and the square-class certificates at the primes `p ≥ 5` dividing every 2×2 minor. -/
structure Wit where
  l₀ : ℤ
  l₁ : ℤ
  l₂ : ℤ
  e₂ : ℕ
  e₃ : ℕ
  sq : List SquareCert

/-- The overlattice obtained by replacing `e_k` by `x / p` (cf. `enlargeGram`). -/
def enlT (C : Tern) (p : ℤ) (k : ℕ) (x₀ x₁ x₂ : ℤ) : Tern :=
  cond (Nat.beq k 0)
    ⟨(x₀ * (C.a * x₀ + C.b * x₁ + C.d * x₂) + x₁ * (C.b * x₀ + C.c * x₁ + C.e * x₂) +
        x₂ * (C.d * x₀ + C.e * x₁ + C.f * x₂)) / (p * p),
      (C.b * x₀ + C.c * x₁ + C.e * x₂) / p, C.c, (C.d * x₀ + C.e * x₁ + C.f * x₂) / p, C.e, C.f⟩
    (cond (Nat.beq k 1)
      ⟨C.a, (C.a * x₀ + C.b * x₁ + C.d * x₂) / p,
        (x₀ * (C.a * x₀ + C.b * x₁ + C.d * x₂) + x₁ * (C.b * x₀ + C.c * x₁ + C.e * x₂) +
          x₂ * (C.d * x₀ + C.e * x₁ + C.f * x₂)) / (p * p),
        C.d, (C.d * x₀ + C.e * x₁ + C.f * x₂) / p, C.f⟩
      ⟨C.a, C.b, C.c, (C.a * x₀ + C.b * x₁ + C.d * x₂) / p, (C.b * x₀ + C.c * x₁ + C.e * x₂) / p,
        (x₀ * (C.a * x₀ + C.b * x₁ + C.d * x₂) + x₁ * (C.b * x₀ + C.c * x₁ + C.e * x₂) +
          x₂ * (C.d * x₀ + C.e * x₁ + C.f * x₂)) / (p * p)⟩)

/-- `x` spans an overlattice of index `p`: `p ∣ C x` and `p² ∣ xᵀ C x`. -/
def enlDiv (C : Tern) (p x₀ x₁ x₂ : ℤ) : Bool :=
  (C.a * x₀ + C.b * x₁ + C.d * x₂) % p == 0 && (C.b * x₀ + C.c * x₁ + C.e * x₂) % p == 0 &&
    (C.d * x₀ + C.e * x₁ + C.f * x₂) % p == 0 &&
    (x₀ * (C.a * x₀ + C.b * x₁ + C.d * x₂) + x₁ * (C.b * x₀ + C.c * x₁ + C.e * x₂) +
      x₂ * (C.d * x₀ + C.e * x₁ + C.f * x₂)) % (p * p) == 0

/-- The digit `k` of `z = 9 z₀ + 3 z₁ + z₂`. -/
def digit3 (z k : ℕ) : ℕ := cond (Nat.beq k 0) (z / 9 % 3) (cond (Nat.beq k 1) (z / 3 % 3) (z % 3))

/-- The local check at `p` with the table test `acc`: `C` itself (code 0) or the overlattice of
pivot `k = (e - 1) mod 3` and vector `z = (e - 1) / 3` with `z_k = 1`. -/
def locOK (acc : Tern → Bool) (p : ℕ) (C : Tern) (e : ℕ) : Bool :=
  cond (Nat.beq e 0) (acc C)
    (Nat.beq (digit3 ((e - 1) / 3) ((e - 1) % 3)) 1 &&
      enlDiv C p (digit3 ((e - 1) / 3) 0) (digit3 ((e - 1) / 3) 1) (digit3 ((e - 1) / 3) 2) &&
      acc (enlT C p ((e - 1) % 3) (digit3 ((e - 1) / 3) 0) (digit3 ((e - 1) / 3) 1)
        (digit3 ((e - 1) / 3) 2)))

/-- The gcd of the 2×2 minors. -/
def minorsGcd (C : Tern) : ℕ := List.rec 0 (fun m _ r => Nat.gcd m.natAbs r) C.minors

/-- The diagonal entry `i` of `C`. -/
def diagT (C : Tern) (i : ℕ) : ℤ := cond (Nat.beq i 0) C.a (cond (Nat.beq i 1) C.c C.f)

/-- The check of a square-class certificate. -/
def sqOK (j : ℕ) (C : Tern) (c : SquareCert) : Bool :=
  Nat.beq (Nat.gcd c.w c.q) 1 && (diagT C c.i - (j * c.w * c.w : ℕ)) % (c.q : ℤ) == 0

/-- The lift `(a, b, c, d, e, f)`. -/
def tern6 (a b c d : ℕ) (e : ℤ) (f : ℕ) : Tern := ⟨a, b, c, d, e, f⟩

/-- The correction `C = G - s λλᵀ` of the lift `pt = (d, e, f)` of `(a, b, c)` by the witness. -/
def witC (s a b c : ℕ) (pt : ℕ × ℤ × ℕ) (w : Wit) : Tern :=
  (tern6 a b c pt.1 pt.2.1 pt.2.2).corr s w.l₀ w.l₁ w.l₂

/-- **The check of a witness** for the lift `(d, e, f)` of `(a, b, c)`: `C > 0`, the local tests
at 2 and 3, and the square classes at the primes `p ≥ 5` dividing every 2×2 minor of `C`. -/
def witOK (j s : ℕ) (acc2 acc3 : BT ℕ) (a b c : ℕ) (pt : ℕ × ℤ × ℕ) (w : Wit) : Bool :=
  decide (0 < (witC s a b c pt w).a) && decide (0 < (witC s a b c pt w).delta) &&
  decide (0 < (witC s a b c pt w).det) &&
  locOK (accepted2 acc2) 2 (witC s a b c pt w) w.e₂ &&
  locOK (accepted3 acc3) 3 (witC s a b c pt w) w.e₃ &&
  Nat.beq (stripL SquareCert.q w.sq (minorsGcd (witC s a b c pt w))) 1 &&
  allR w.sq (sqOK j (witC s a b c pt w))

/-! ### Decoding the certificates -/

/-- `cnt` entries `(q, kind, w)` of 40 bits (16, 2 and 16 bits). -/
def decF (n cnt : ℕ) : List FactorEntry :=
  Nat.rec (motive := fun _ => ℕ → List FactorEntry) (fun _ => [])
    (fun _ r m => ⟨m &&& 65535, (m >>> 16) &&& 3, (m >>> 18) &&& 65535⟩ :: r (m >>> 40)) cnt n

/-- An option: `x`, `|y|` (4 bits each), `y < 0` (1 bit), `g` (8 bits), the number of entries
(4 bits), and the entries from bit 21. -/
def decOpt (n : ℕ) : TermOpt :=
  ⟨n &&& 15, (n >>> 4) &&& 15, n.testBit 8, (n >>> 9) &&& 255, decF (n >>> 21) ((n >>> 17) &&& 15)⟩

/-- The options of a block. -/
def decOpts (l : List ℕ) : List TermOpt := List.rec [] (fun n _ r => decOpt n :: r) l

/-- A square-class entry `(q, i, w)` of 12 bits (5, 2 and 5 bits), none if `q = 0`. -/
def decSq (m : ℕ) : List SquareCert :=
  cond (Nat.beq (m &&& 31) 0) [] [⟨m &&& 31, (m >>> 5) &&& 3, (m >>> 7) &&& 31⟩]

/-- A witness (64 bits): `λᵢ + 2` (3 bits each), `e₂`, `e₃` (7 bits each), and two square-class
entries. -/
def decW (n : ℕ) : Wit :=
  ⟨((n &&& 7 : ℕ) : ℤ) - 2, (((n >>> 3) &&& 7 : ℕ) : ℤ) - 2, (((n >>> 6) &&& 7 : ℕ) : ℤ) - 2,
    (n >>> 9) &&& 127, (n >>> 16) &&& 127, decSq (n >>> 23) ++ decSq (n >>> 35)⟩

/-! ### A block -/

/-- The classes not covered below `D₀`. -/
def pendB (acc2 acc3 : BT ℕ) (s a b c dom maxm : ℕ) (opts : List TermOpt) : ℕ :=
  dom ^^^ (dom &&& coverAll acc2 acc3 s a b c maxm (dZero a b c) opts)

/-- The checks of a block with its pending classes. -/
def termCore (j s : ℕ) (acc2 acc3 : BT ℕ) (maxm pend a b c U : ℕ) (opts : List TermOpt)
    (wits : ℕ) : Bool :=
  allR opts (optOK j s a b c) &&
  cond (Nat.beq pend 0) true
    (Nat.beq (pend &&& (pend ^^^ (pend &&& coverAll acc2 acc3 s a b c maxm (U + 1) opts))) 0 &&
      idxAll (liftsOf a b c U pend maxm) fun i pt =>
        witOK j s acc2 acc3 a b c pt (decW (tget wits 64 i)))

/-- The certificate of a block: the bound `U = U(B)`, the options (packed, `decOpt`) and the
witnesses (packed, 64 bits each, `decW`). -/
structure TermCert where
  U : ℕ
  opts : List ℕ
  wits : ℕ

/-- The residues modulo 9 maximal at 3 with leading block `(a, b, c)`. -/
def maxmOf (mx a b c : ℕ) : ℕ := tget mx 729 (blk3 (a % 9) (b % 9) (c % 9))

/-- **The terminal check of a block** with its certificate. -/
def termOK (j s : ℕ) (acc2 acc3 : BT ℕ) (r2 mx a b c : ℕ) (cert : TermCert) : Bool :=
  termCore j s acc2 acc3 (maxmOf mx a b c)
    (pendB acc2 acc3 s a b c (domainB r2 (maxmOf mx a b c) a b c) (maxmOf mx a b c)
      (decOpts cert.opts))
    a b c cert.U (decOpts cert.opts) cert.wits

/-- The blocks `(a, b, c)` of the groups `((a, t), [(b, c), …])` left by the first pass. -/
def flatBlocks (L : List ((ℕ × ℕ) × List (ℕ × ℕ))) : List (ℕ × ℕ × ℕ) :=
  List.rec [] (fun e _ r => List.rec r (fun bc _ r' => (e.1.1, bc.1, bc.2) :: r') e.2) L

/-- **The terminal checks of batch `i`** of a list of blocks cut into batches of the given
sizes. -/
def termBatch (j s : ℕ) (acc2 acc3 : BT ℕ) (r2 mx : ℕ) (blocks : List (ℕ × ℕ × ℕ))
    (sizes : List ℕ) (i : ℕ) (certs : List TermCert) : Bool :=
  zipOK (fun x cert => termOK j s acc2 acc3 r2 mx x.1 x.2.1 x.2.2 cert)
    ((blocks.drop (sizes.take i).sum).take (sizes.getD i 0)) certs

end KimKimOh

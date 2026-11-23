import KimKimOh.Tables.Profiles3
import KimKimOh.Compute.Windows

/-!
# The options of a local case and the bounds `high` (computational definitions)
-/

namespace KimKimOh

open Tables

/-- The primes from 5 below 73. -/
def bigPrimes72 : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

/-- The primes from 5 dividing `a < 73`. -/
def primesOf (a : ℕ) : List ℕ := bigPrimes72.filter fun p => a % p == 0

/-- The signed divisors of 6. -/
def sdiv6 : List ℤ := [1, 2, 3, 6, -1, -2, -3, -6]

/-- `c - s y²` is 0 or in the square class of `j` modulo `p`. -/
def sqClassOK (j s p : ℕ) (c y : ℤ) : Bool :=
  (c - s * y * y) % p == 0 ||
    (List.range p).any fun u => u != 0 && ((c - s * y * y) - j * u * u) % p == 0

/-- For every residue `c` modulo the primes from 5 dividing `a` and every start modulo `h`,
some signed divisor of 6 in the progression passes the extra condition of `sec:high`. -/
def sdivOK (j s a h : ℕ) : Bool :=
  (List.range (primesOf a).prod).all fun c => (List.range h).all fun st =>
    sdiv6.any fun y => (y - st) % h == 0 &&
      (primesOf a).all fun p => (c : ℤ) % p == 0 || sqClassOK j s p c y

/-- The tested values of `x`. -/
def xList : List ℕ := [0, 1, 2, 3, 6]

/-- The options `(x, h, d)` of a local case: steps combined from options at `x mod 2` and
`x mod 3`; `x = 0` only when `a₀ < 73`. -/
def optsOf (a₀ : ℕ) (P₂ P₃ : List (List (ℕ × ℕ))) : List (ℕ × ℕ × ℕ) :=
  xList.flatMap fun x => if x != 0 || a₀ < 73 then
    (P₂.getD (x % 2) []).flatMap fun o₂ => (P₃.getD (x % 3) []).map fun o₃ =>
      (x, (normOpt 2 o₂).1 * (normOpt 3 o₃).1, (normOpt 2 o₂).2 * (normOpt 3 o₃).2)
  else []

/-- An option is valid: `s x² < a₀`, and the signed-divisor test when `x = 0`. -/
def validOpt (j s a₀ : ℕ) (o : ℕ × ℕ × ℕ) : Bool :=
  s * o.1 * o.1 < a₀ && (o.1 != 0 || sdivOK j s a₀ o.2.1)

/-- The width `W`: `h g` for `x > 0`, and `12` for `x = 0`. -/
def widthW (g : ℕ) (o : ℕ × ℕ × ℕ) : ℕ := if o.1 = 0 then 12 else o.2.1 * g

/-- `⌊s a a₀ (3W² + 4 d² g²) / (12 (a₀ - s x²))⌋`: the option works when `δ` exceeds it. -/
def thr (s a a₀ g : ℕ) (o : ℕ × ℕ × ℕ) : ℕ :=
  s * a * a₀ * (3 * widthW g o ^ 2 + 4 * (o.2.2 * g) ^ 2) / (12 * (a₀ - s * o.1 * o.1))

/-- The local cases from lists of profiles at 2 and 3. -/
def pairsOf (L₂ L₃ : List (List (List (ℕ × ℕ)))) :
    List (List (List (ℕ × ℕ)) × List (List (ℕ × ℕ))) :=
  L₂.flatMap fun P₂ => L₃.map fun P₃ => (P₂, P₃)

def validOpts (j s a₀ : ℕ) (P₂ P₃ : List (List (ℕ × ℕ))) : List (ℕ × ℕ × ℕ) :=
  (optsOf a₀ P₂ P₃).filter (validOpt j s a₀)

/-- The least element of a list (`0` for the empty list). -/
def minL : List ℕ → ℕ
  | [] => 0
  | x :: l => l.foldl min x

/-- Every local case has a valid option. -/
def pairsOK (j s : ℕ) (L₂ L₃ : List (List (List (ℕ × ℕ)))) (a₀ : ℕ) : Bool :=
  (pairsOf L₂ L₃).all fun pr => !(validOpts j s a₀ pr.1 pr.2).isEmpty

/-- **`a H_j(a₀, t)`, rounded down**: the largest over the local cases of the least threshold over
the valid options. -/
def high (j s : ℕ) (L₂ L₃ : List (List (List (ℕ × ℕ)))) (a a₀ t : ℕ) : ℕ :=
  (pairsOf L₂ L₃).foldl (fun m pr =>
    max m (minL ((validOpts j s a₀ pr.1 pr.2).map (thr s a a₀ (Windows.gWin t))))) 0

end KimKimOh

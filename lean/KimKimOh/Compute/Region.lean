import KimKimOh.Compute.HighBound
import KimKimOh.Compute.Primes

/-!
# The class bounds and the table of block bounds (computational definitions)
-/

namespace KimKimOh

open Tables Primes

/-- `P_t` computed from `qList` (`P_eq`, for `t ≤ 28`). -/
def Pc (t : ℕ) : ℕ := (qList.take t).prod

/-- The least representative `a₀ ∈ [73, 84]` of `a mod 12`, for `a ≥ 73`. -/
def a0Of (a : ℕ) : ℕ := 73 + (a - 73) % 12

/-- The numerator `N' = s a₀ (3W² + 4 d² g²)` and denominator `D = 12 (a₀ - s x²)` of
`H(a₀, t)` for an option. -/
def numO (s a₀ g : ℕ) (o : ℕ × ℕ × ℕ) : ℕ := s * a₀ * (3 * widthW g o ^ 2 + 4 * (o.2.2 * g) ^ 2)

def denO (s a₀ : ℕ) (o : ℕ × ℕ × ℕ) : ℕ := 12 * (a₀ - s * o.1 * o.1)

/-- `⌊4 N' / 3 D⌋`: the option works for `a > ⌊4 N' / 3 D⌋` (with `3 a² ≤ 4 δ`). -/
def aBound (s a₀ g : ℕ) (o : ℕ × ℕ × ℕ) : ℕ := 4 * numO s a₀ g o / (3 * denO s a₀ o)

/-- `4 H(a₀, t) / 3`, rounded down: the largest over the local cases of the least `aBound`. -/
def Acap (j s : ℕ) (L₂ L₃ : List (List (List (ℕ × ℕ)))) (a₀ t : ℕ) : ℕ :=
  (pairsOf L₂ L₃).foldl (fun m pr =>
    max m (minL ((validOpts j s a₀ pr.1 pr.2).map (aBound s a₀ (Windows.gWin t))))) 0

/-- `3 P_t > 4 H(a₀, t)²`: every local case has a valid option with `3 P_t D² > 4 N'²`. -/
def classSkip (j s : ℕ) (L₂ L₃ : List (List (List (ℕ × ℕ)))) (a₀ t : ℕ) : Bool :=
  (pairsOf L₂ L₃).all fun pr => (validOpts j s a₀ pr.1 pr.2).any fun o =>
    Nat.blt (4 * numO s a₀ (Windows.gWin t) o ^ 2) (3 * Pc t * denO s a₀ o ^ 2)

/-- The 4-bit index of a chunk in a packed table. -/
def pget (tab blk : ℕ) : ℕ := (tab >>> (4 * blk)) &&& 15

/-- The bound for the mask classes `(i₂, i₃)`, capped at `P_{t+1}`. -/
def hiEntry (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (ml2 ml3 : ℕ → List ℕ)
    (a t i₂ i₃ : ℕ) : ℕ :=
  min (high j s (maskedProfs (prof2 (a % 4)) ((ml2 (a % 4)).getD i₂ 0))
    (maskedProfs (prof3 (a % 3)) ((ml3 (a % 3)).getD i₃ 0)) a a t) (Pc (t + 1))

/-- `n` values of `w` bits packed into one natural number, value `i` at bit `w i`. -/
def packF (w n : ℕ) (v : ℕ → ℕ) : ℕ := Nat.rec 0 (fun i acc => acc + (v i <<< (w * i))) n

/-- **The table of bounds for `(a, t)`**: the entries `hiEntry` in fields of 160 bits, at index
`16 i₂ + i₃` (at most 16 mask classes at each prime). Each entry is at most `P_{t+1} < 2¹⁶⁰`
(`Pc_lt`). -/
def hiTab (j s : ℕ) (prof2 prof3 : ℕ → List (List (List (ℕ × ℕ)))) (ml2 ml3 : ℕ → List ℕ)
    (a t : ℕ) : ℕ :=
  packF 160 256 fun i => hiEntry j s prof2 prof3 ml2 ml3 a t (i / 16) (i % 16)

/-- The bound of the block `(a, b, c)` from the table. -/
def hiOf (tab pi2 pi3 a b c : ℕ) : ℕ :=
  (tab >>> (160 * (16 * pget pi2 (blk2 (a % 8) (b % 4) (c % 8)) +
    pget pi3 (blk3 (a % 9) (b % 9) (c % 9))))) &&& (2 ^ 160 - 1)

end KimKimOh

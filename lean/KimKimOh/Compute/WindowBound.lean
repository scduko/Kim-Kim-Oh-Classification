import Mathlib.Data.List.Basic
import Mathlib.Util.CompileInductive

/-!
# The window bound of the first pass (computational definitions)
-/

namespace KimKimOh

/-- The primes from 5 to 47. -/
def smallPrimes : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

/-- Their product. -/
def prim47 : ℕ := 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41 * 43 * 47

/-- The small primes dividing `Δ`, from `gs = gcd(Δ, prim47)`: none if `gs = 1`, `gs` itself if
`gs < 35 = 5 · 7` (then `gs` is a single prime), and otherwise by trial division. -/
def smallOf (gs : ℕ) : List ℕ :=
  cond (gs == 1) [] (cond (Nat.blt gs 35) [gs]
    (List.rec [] (fun p _ r => cond (gs % p == 0) (p :: r) r) smallPrimes))

/-- An upper bound for the number of primes `≥ 53` whose product is at most `n`, from the powers
`53, 53², 53³, 53⁴`; the bound `n` itself is used above `53⁴`. -/
def largeBound (n : ℕ) : ℕ :=
  cond (Nat.blt n 53) 0 (cond (Nat.blt n 2809) 1 (cond (Nat.blt n 148877) 2
    (cond (Nat.blt n 7890481) 3 n)))

/-- The weight: 2 if `p ∣ δ` and `p ∤ cnt`, else 1. -/
def wtN (δ cnt p : ℕ) : ℕ := cond (δ % p == 0 && !(cnt % p == 0)) 2 1

/-- **The bound for the sieve sum at `g`** (Lemma A.1): `Σ_{p ∣ Δ} w_p ⌈g/p⌉`, with the primes
`p ≤ 47` listed and the primes `p ≥ 53` counted by `largeBound`, each with `⌈g/p⌉ ≤ ⌈g/53⌉`. The
weight-2 primes `p ≥ 53` divide `gcd(Δ, δ)` and are counted a second time. -/
def ubound (Δ δ cnt g : ℕ) : ℕ :=
  List.rec 0 (fun p _ r => wtN δ cnt p * ((g + p - 1) / p) + r) (smallOf (Nat.gcd Δ prim47)) +
    (largeBound (Δ / Nat.gcd Δ prim47) + largeBound (Nat.gcd Δ δ)) * ((g + 52) / 53)

end KimKimOh

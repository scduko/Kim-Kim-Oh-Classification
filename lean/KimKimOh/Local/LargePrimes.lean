import KimKimOh.Local.OddPrime

/-!
# `lem:functional` at the primes `p ≥ 5`

At `p ≥ 5`, where `K₃` and `K₉` are unimodular, a ternary is represented over `ℤ_p` if it has
rank at least 2 modulo `p` (`rank_K3`, `rank_K9`), or if one of its diagonal entries lies in
the square class of `j = det K_j` modulo `p` (`square_K3`, `square_K9`). Local representation is
`LocallyRepresents`: congruences modulo every power of `p`.

Each of `K₃, K₉` is `hostForm α s q r` up to the order of its basis (`K3_embed`, `K9_embed`),
with invariants `α, s, sr - q²` equal to `(1, 2, 3)` and `(3, 2, 3)`. A prime `p ≥ 5` divides
none of them, so the lattice is `H ⊥ H ⊥ ⟨det⟩` over `ZMod p` and the two criteria hold there
(`rank_of_hostForm`, `square_of_hostForm`, in `Local/OddPrime.lean`); Hensel's lemma lifts them
(`Local/Hensel.lean`).
-/

namespace KimKimOh

open Local Local.OddPrime

/-- **`lem:functional` at `p ≥ 5`, rank criterion, for `K₃`.** -/
theorem rank_K3 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (g : Tern) (hg : g.RankGeTwoMod p) :
    LocallyRepresents K3.gram g.toMatrix p :=
  rank_of_hostForm K3_embed (by norm_num) p hp h5 g hg

/-- **`lem:functional` at `p ≥ 5`, rank criterion, for `K₉`.** -/
theorem rank_K9 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (g : Tern) (hg : g.RankGeTwoMod p) :
    LocallyRepresents K9.gram g.toMatrix p :=
  rank_of_hostForm K9_embed (by norm_num) p hp h5 g hg

/-- **`lem:functional` at `p ≥ 5`, square-class criterion, for `K₃`.** -/
theorem square_K3 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (g : Tern) (hg : g.HasDiagSquareClass 3 p) :
    LocallyRepresents K3.gram g.toMatrix p :=
  square_of_hostForm K3_embed (by norm_num) (by norm_num) p hp h5 g hg

/-- **`lem:functional` at `p ≥ 5`, square-class criterion, for `K₉`.** -/
theorem square_K9 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (g : Tern) (hg : g.HasDiagSquareClass 9 p) :
    LocallyRepresents K9.gram g.toMatrix p :=
  square_of_hostForm K9_embed (by norm_num) (by norm_num) p hp h5 g hg

end KimKimOh

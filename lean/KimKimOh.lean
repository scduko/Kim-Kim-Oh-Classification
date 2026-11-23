import KimKimOh.Main
import KimKimOh.AxiomAudit

/-!
# 3-universal lattices of rank 6, and a quinary exception

A Lean formalization of Theorem 1.2 of the manuscript *Completing the Kim–Kim–Oh classification of
minimal-rank `n`-universal lattices*:

1. `I₃ ⊥ A₁ ⊥ A₂` is 3-universal;
2. `I₃ ⊥ A₂ ⊥ ⟨3⟩` is 3-universal;
3. `I₆ ⊥ A₂` is not 5-universal.

The statement is `KimKimOh.MainTheorem` (`KimKimOh/Statement.lean`), and `KimKimOh.mainTheorem`
(`KimKimOh/Main.lean`) proves it without hypotheses. Two classical results come from Jonathan
Hanke's QuadFormsKB (vendored in `QuadFormsKB/`): the genus representation theorem and the
Conway–Sloane mass formula. From them, the local–global principle for `K₃` and `K₉`
(`KimKimOh/Bridge/LocalGlobal.lean`) and the 2-universality of `⟨1, 1, 3⟩ ⊥ A₂` and
`⟨1, 1, 2⟩ ⊥ A₂` (Kim–Kim–Oh, Theorem 1; `KimKimOh/Genus/Kko113.lean`, `KimKimOh/Genus/Kko112.lean`)
are proved. Part 3 has a short proof of its own (`not_isUniversal_I6A2`).
-/

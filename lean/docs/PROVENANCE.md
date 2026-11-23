# Sources

## The manuscript and its supplement

The numbering of results, tables, certificates, and equations follows the
manuscript by Scott Duke Kominers. The Lean docstrings also give the manuscript’s
LaTeX labels. The [correspondence guide](PAPER_CORRESPONDENCE.md) matches the results with their Lean proofs.

The [computational supplement](../../python/README.md) contains the Python search in `verification/`, the five certificates in `certificates/`, the checker in `audit/`, and the reference transcripts in `expected_output/`.

## Data generated from the supplement

Every datum in the Lean source is checked by the kernel, so none of it has to be trusted. The
generators of `scripts/` write it, and reproduce the committed files byte for byte
(`scripts/README.md`).

- **Local tables** (`KimKimOh/Tables/Data/T{32,33,92,93}.lean`): the accepted residues `ℛ_{j,p}` of
  Appendix A.1 with one witness per orbit, from the dynamic program
  `scripts/tables/witdp.c`. They do not depend on the supplement; the counts agree with Table 3.
- **Profiles and chunk tables** (`Tables/Data/ProfileData.lean`, `Tables/Data/ChunkData.lean`): the
  profiles of Appendix A.2, computed from the supplement’s local tables and profile routines. Its Python checker compares the resulting profile counts with `certificates/local_progression_steps.tsv`.
- **The first pass** (`KimKimOh/FirstPassChecks/`): the pairs `(a, t)` to enumerate and the blocks
  that fail the whole-block test. These come from the Lean definitions themselves, evaluated by
  `scripts/firstpass/Heavy.lean` and `RegionEval.lean`, whose outputs are committed in
  `scripts/firstpass/data/`. The counts (536 and 1,136 pairs; 836 and 5,147 blocks) are those of
  Certificates 4.2 and 4.3(a).
- **The last-column test** (`Tables/Data/TermTables.lean`, `KimKimOh/Terminal/`): a certificate for
  every block left by the first pass, with its options and witnesses, from the supplement's records
  `audit/coverage.json.gz` and `audit/witnesses.jsonl.gz` (copies of
  `certificates/last_column_bounds.json.gz` and `certificates/representation_witnesses.jsonl.gz`),
  read through the supplement's own checker.

## Data computed for this formalization

- **Binary sources** (`KimKimOh/Local/BinaryData.lean`, by `scripts/genus/gen_local_binary.py`):
  witnesses modulo 8 and 9 for the local 2-universality of `K₉`.
- **`⟨1, 1, 2⟩ ⊥ A₂`** (`KimKimOh/Genus/Kko112Data.lean`, `Kko112HardData.lean`, by
  `scripts/genus/gen_kko112.py`): local witnesses, and the transfer matrices from `⟨6⟩ ⊥ I₄`
  (Section 4, Lemma 1 of [Kim, Kim, and Oh (1999)](../../README.md#reference)).
- **Automorphism groups** (`Genus/K3K9Symbols.lean`, `Genus/Kko112Genus.lean`): the elements of
  `Aut(A₂)`, `Aut(A₂ ⊥ ⟨3⟩)`, `Aut(A₂ ⊥ ⟨2⟩)` and `Aut⟨6⟩`, listed and certified complete by a box
  enumeration.

## Classical results

The manuscript cites two classical results; both are proved here, from Jonathan Hanke's library
QuadFormsKB.

- **Lemma 2.1, global part**: a ternary lattice represented by `K₃ = I₃ ⊥ A₂` or
  `K₉ = I₂ ⊥ A₂ ⊥ ⟨3⟩` over every `ℤ_p` is represented by it. Both genera have one class:
  their masses are `1/576` and `1/192` by the Conway–Sloane mass formula, and the automorphism
  groups have orders `576` and `192`. With the genus representation theorem this gives
  `localGlobal_K3` and `localGlobal_K9` (`KimKimOh/Bridge/LocalGlobal.lean`).
- **Theorem 1.1 for `⟨1, 1, 3⟩ ⊥ A₂` and `⟨1, 1, 2⟩ ⊥ A₂`** (Kim–Kim–Oh): both are
  2-universal (`kko113_universal`, `kko112_universal`). The first is `K₉` up to isometry. For the
  second, the genus has two classes, `K₂₂` and `K₆ = ⟨6⟩ ⊥ I₄`; the formalization follows
  the argument in Section 4, Lemmas 1–3 of [Kim, Kim, and Oh (1999)](../../README.md#reference), with a kernel check for the reduced binaries `[a, b, c]`
  with `a ≤ 72` and `ac - b² ≤ 72a`.

The results used from QuadFormsKB, all proved there:

| Result | QuadFormsKB | Used in |
| --- | --- | --- |
| Genus representation theorem (O'Meara 102:5 over `ℤ`) | `Watson1963.exists_sameGenus_rep` | `Genus/Kko112Genus.lean` |
| Class number 1 gives the local–global principle | `Watson1963.rep_of_encard_le_one` | `Genus/K3K9.lean` |
| Conway–Sloane mass formula | `mass_eq_stdMass_mul_symbols_unconditional`, `pMassOdd`, `pMassTwo` | `Genus/K3K9Symbols.lean`, `Genus/K3K9.lean`, `Genus/Kko112Genus.lean` |
| The classes of a genus from its mass | `genusClasses_eq_of_sum_eq_mass`, `exists_intEquiv_of_sum_eq_mass` | `Genus/K3K9.lean`, `Genus/Kko112Genus.lean` |
| Automorphism counts by certified enumeration | `card_aut_eq_of_cert`, `card_aut_sumI` | `Genus/K3K9Symbols.lean`, `Genus/Kko112Genus.lean` |

## QuadFormsKB

Jonathan Hanke, *Quadratic forms over number fields in Lean 4 (QuadFormsKB)*, version 0.6.1,
upstream commit `43bd018`, Apache License 2.0, <https://github.com/jonhanke/quadratic-forms-lean>
(DOI 10.5281/zenodo.23509792). `QuadFormsKB/` holds the modules that this formalization imports,
directly or indirectly, ported from Lean 4.35 / Mathlib v4.35.0 to Lean 4.36 / Mathlib v4.36.0.
`QuadFormsKB/PORT.md` describes the changes, and each changed file says so in its first line.
See the [QuadFormsKB license](../QuadFormsKB/LICENSE) and the [repository notice](../../NOTICE).

## Kernel replay

The per-module replay in [`scripts/ReplayModule.lean`](../scripts/ReplayModule.lean) is adapted from
Lean 4.36.0’s `src/LeanChecker.lean`, by Kim Morrison and Sebastian Ullrich, under the Apache License 2.0.

## The cited literature

- [Kim, Kim, and Oh (1999)](../../README.md#reference). Theorem 1.1 of the manuscript draws on
  their Theorem 1 and Proposition 3. Their Section 4 treats the two quinary lattices discussed above.
- B.-K. Oh, *Universal ℤ-lattices of minimal rank*, Proc. Amer. Math. Soc. 128 (2000), 683–689:
  the minimal rank and the minimal-rank lattices for `6 ≤ n ≤ 8`.
- O. T. O'Meara, *Introduction to Quadratic Forms*, Classics in Mathematics, Springer, 2000:
  102:5.
- J. H. Conway, N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*, Proc. Roy. Soc.
  London Ser. A 419 (1988), 259–286.

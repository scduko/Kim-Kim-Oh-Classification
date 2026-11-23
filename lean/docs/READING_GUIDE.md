# Reading guide

Every module of the formalization of Theorem 1.2, with the title of its module docstring. Within each group the modules are in dependency order: a module comes after the modules it imports. The module docstrings state the results and name the theorems. This file is generated from them.

## Statement and assembly

The statement, the lattices of the paper, and the proof of Theorem 1.2 from its parts.

| Module | Contents |
| --- | --- |
| `KimKimOh/Lattices.lean` | The lattices of the paper |
| `KimKimOh/Statement.lean` | Statement of the main theorem |
| `KimKimOh/Hosts.lean` | The quinary lattices `K_j` (`eq:pairs`) |
| `KimKimOh/Assembly.lean` | Assembling Theorem 1.2 |
| `KimKimOh/Main.lean` | Theorem 1.2 |
| `KimKimOh/AxiomAudit.lean` | The axiom audit command |
| `KimKimOh.lean` | 3-universal lattices of rank 6, and a quinary exception |

## Lattices as Gram matrices

Positive-definite integral lattices, isometries, representations, reduced bases.

| Module | Contents |
| --- | --- |
| `KimKimOh/GramLattice.lean` | Positive-definite integral lattices as Gram matrices |
| `KimKimOh/GramLattice/Isometry.lean` | Isometry, the bilinear form, and pullbacks |
| `KimKimOh/Maximal.lean` | Maximal lattices and local representations |
| `KimKimOh/Ternary.lean` | Ternary Gram matrices in the coordinates of §3 |
| `KimKimOh/Reduced.lean` | Reduced bases of ternary lattices (§3) |
| `KimKimOh/Overlattice.lean` | Maximal ternary lattices (§2, `eq:maximal`) |
| `KimKimOh/Roots.lean` | Roots of `Iₙ` and the form of `A₂` |
| `KimKimOh/SmallPrimes.lean` | Primes at least 5 |
| `KimKimOh/GramLattice/BinaryReduction.lean` | Reduced binary lattices |
| `KimKimOh/MaximalMod.lean` | A maximal ternary is nonzero modulo every prime (§2, after `eq:maximal`) |

## Theorem 1.2(iii): the quinary exception (§5)

| Module | Contents |
| --- | --- |
| `KimKimOh/Quinary/Core.lean` | Proposition 5.1 (`prop:exception`): `I₆ ⊥ A₂` does not represent `Λ₁₁₇` |
| `KimKimOh/Quinary.lean` | Theorem 1.2(iii): `I₆ ⊥ A₂` is not 5-universal (`sec:five`) |

## From QuadFormsKB: genera and the local–global principle

The bridge from `GramLattice` to Hanke's integral forms, the genera of `K₃`, `K₉` and of `⟨1, 1, 2⟩ ⊥ A₂`, and the cases of Kim–Kim–Oh's Theorem 1 used by the paper.

| Module | Contents |
| --- | --- |
| `KimKimOh/Bridge/Padic.lean` | Local representations modulo every `pᵏ` are `p`-adic representations |
| `KimKimOh/Genus/K3K9Symbols.lean` | `K₃` and `K₉`: genus symbols, local masses, automorphism counts |
| `KimKimOh/Bridge/Transfer.lean` | From `GramLattice` to Hanke's integral forms |
| `KimKimOh/Genus/K3K9.lean` | Class number 1 of `K₃` and `K₉`, and the local–global principle for them |
| `KimKimOh/Bridge/LocalGlobal.lean` | `lem:functional`, global part |
| `KimKimOh/Genus/Kko113.lean` | Kim–Kim–Oh, Theorem 1, for `⟨1, 1, 3⟩ ⊥ A₂` |
| `KimKimOh/Genus/Kko112HardData.lean` | Data for the doubly hard binaries of `⟨1, 1, 2⟩ ⊥ A₂` (generated) |
| `KimKimOh/Genus/Kko112Data.lean` | Data for `⟨1, 1, 2⟩ ⊥ A₂` (generated) |
| `KimKimOh/Genus/Kko112Local.lean` | `⟨1, 1, 2⟩ ⊥ A₂` is locally 2-universal |
| `KimKimOh/Genus/Kko112HardLocal.lean` | Doubly hard binaries: through `N = ⟨1, 1⟩ ⊥ A₂` |
| `KimKimOh/Genus/Kko112Sieve.lean` | A sieve for Kim–Kim–Oh, §4 |
| `KimKimOh/Genus/Kko112Hard.lean` | Doubly hard binaries are represented by `⟨1, 1, 2⟩ ⊥ A₂` (Kim–Kim–Oh, §4) |
| `KimKimOh/Genus/Kko112Genus.lean` | The genus of `K₂₂ = ⟨1, 1, 2⟩ ⊥ A₂`: two classes |
| `KimKimOh/Genus/Kko112FromK6.lean` | From `K₆` to `K₂₂`: Lemma 1 of Kim–Kim–Oh, §4 |
| `KimKimOh/Genus/Kko112.lean` | Kim–Kim–Oh, Theorem 1, for `⟨1, 1, 2⟩ ⊥ A₂` |

## Local representations (§2, `lem:functional`, `lem:local-precision`)

| Module | Contents |
| --- | --- |
| `KimKimOh/Local/BinaryData.lean` | Local witnesses for binary sources (generated) |
| `KimKimOh/Local/Basic.lean` | Local representations and the shape of the hosts |
| `KimKimOh/Local/Hensel.lean` | Hensel's lemma for representations of quadratic forms |
| `KimKimOh/Local/Precision.lean` | `lem:local-precision` |
| `KimKimOh/Local/Diagonal.lean` | The diagonal bases at 2 and 3 (§2) |
| `KimKimOh/Local/OddPrime.lean` | Seeds over finite fields (`lem:functional`) |
| `KimKimOh/Local/LargePrimes.lean` | `lem:functional` at the primes `p ≥ 5` |
| `KimKimOh/Local/Binary.lean` | Binary sources: `K₉` is locally 2-universal |

## The correction and the choice of coefficients (§3, §4.1)

| Module | Contents |
| --- | --- |
| `KimKimOh/Correction.lean` | The correction `C = G - s λλᵀ` (`eq:highcost`, `eq:sectionbound`) |
| `KimKimOh/ExcludedClasses.lean` | Excluded residue classes |
| `KimKimOh/ScalarSlice.lean` | `lem:scalar-slice` |
| `KimKimOh/Compute/Primes.lean` | The primes from 5 to 113 (computational definition) |
| `KimKimOh/Primes.lean` | The primes from 5 (`sec:high`) |
| `KimKimOh/Compute/Windows.lean` | The windows `g_t` (computational definitions) |
| `KimKimOh/Windows.lean` | Sieve windows for arithmetic progressions (`sec:high`, `app:prescriptions`) |
| `KimKimOh/Choice.lean` | Choosing the two coefficients (`sec:high`) |
| `KimKimOh/Compute/HighBound.lean` | The options of a local case and the bounds `high` (computational definitions) |
| `KimKimOh/HighBound.lean` | The bounds `H_j(a, t)` (`sec:high`, `app:prescriptions`) |

## Local tables and profiles at 2 and 3 (`app:correction-tests`, `app:prescriptions`)

Generated data (`Tables/Data/`) and its kernel checks (`Tables/Check*`, `Tables/ProfCheck*`).

| Module | Contents |
| --- | --- |
| `KimKimOh/Tables/Bits.lean` | Bitsets for the local tables (`app:correction-tests`) |
| `KimKimOh/Tables/Accept3.lean` | Certified local tables at 3 (`app:correction-tests`) |
| `KimKimOh/Tables/Accept2.lean` | Certified local tables at 2 (`app:correction-tests`) |
| `KimKimOh/Tables/Profiles3.lean` | The sets `𝒰_{j,3}(σ)` and the profiles at 3 (`sec:high`, `app:correction-tests`, `app:prescriptions`) |
| `KimKimOh/Tables/Profiles2.lean` | The sets `𝒰_{j,2}(σ)` and the profiles at 2 (`app:correction-tests`, `app:prescriptions`) |
| `KimKimOh/Tables/Data/ChunkData.lean` | Per-chunk profile masks and worst-step tables (generated) |
| `KimKimOh/Tables/Data/ProfileData.lean` | Profiles of the maximal residues (generated) |
| `KimKimOh/HostDataChecks.lean` | Kernel checks of the data of the two host decompositions |
| `KimKimOh/Tables/Data/T32.lean` | The local table of K₃ at 2 (generated) |
| `KimKimOh/Tables/ProfCheck32.lean` | The kernel check of the profiles and k-steps of K₃ at 2 (generated) |
| `KimKimOh/Tables/Data/T33.lean` | The local table of K₃ at 3 (generated) |
| `KimKimOh/Tables/ProfCheck33_0.lean` … `_8` | The kernel check of the profiles and k-steps of K₃ at 3 (generated) (9 modules) |
| `KimKimOh/Tables/Data/T92.lean` | The local table of K₉ at 2 (generated) |
| `KimKimOh/Tables/ProfCheck92.lean` | The kernel check of the profiles and k-steps of K₉ at 2 (generated) |
| `KimKimOh/Tables/Data/T93.lean` | The local table of K₉ at 3 (generated) |
| `KimKimOh/Tables/ProfCheck93_0.lean` … `_8` | The kernel check of the profiles and k-steps of K₉ at 3 (generated) (9 modules) |
| `KimKimOh/Tables/ProfChecks.lean` | The chunk checks of both hosts at 2 and 3 |
| `KimKimOh/Tables/Check32.lean` | The kernel check of the local table of K₃ at 2 (generated) |
| `KimKimOh/Tables/Check92.lean` | The kernel check of the local table of K₉ at 2 (generated) |
| `KimKimOh/Tables/Check33.lean` | The kernel check of the local table of K₃ at 3 (generated) |
| `KimKimOh/Tables/Check93.lean` | The kernel check of the local table of K₉ at 3 (generated) |
| `KimKimOh/Tables/Soundness.lean` | The local tests at 2 and 3 (`app:correction-tests`) |
| `KimKimOh/HostData.lean` | The two host decompositions |
| `KimKimOh/Tables/Data/TermTables.lean` | The tables of the last-column test (generated) |

## The finite part (§4.2, `sec:finite`, `app:bounded`)

The first pass, the region, the enumeration and the last-column test, with the kernel loops. The `Compute/` modules hold the computational definitions; their specifications are proved in the module of the same name outside `Compute/`.

| Module | Contents |
| --- | --- |
| `KimKimOh/Compute/Loops.lean` | Loops for the kernel (computational definitions) |
| `KimKimOh/Loops.lean` | Specifications of the kernel loops |
| `KimKimOh/FirstPass.lean` | The first pass of `sec:finite`: one direction for a whole binary block |
| `KimKimOh/Compute/WindowBound.lean` | The window bound of the first pass (computational definitions) |
| `KimKimOh/WindowBound.lean` | A computable bound for the sieve sum of the first pass |
| `KimKimOh/Compute/Pass.lean` | The first-pass test of a block, and its kernel-fast copy (computational definitions) |
| `KimKimOh/PassCheck.lean` | The kernel test of a binary block in the first pass |
| `KimKimOh/Compute/Region.lean` | The class bounds and the table of block bounds (computational definitions) |
| `KimKimOh/Region.lean` | The region of binary blocks left by `sec:high` |
| `KimKimOh/RegionCover.lean` | Every exception lies in the region (`sec:high`, `sec:finite`, `app:prescriptions`) |
| `KimKimOh/Compute/Enum.lean` | The enumeration of the region (computational definitions) |
| `KimKimOh/Enum.lean` | Enumerating the region (`sec:finite`, `app:bounded`) |
| `KimKimOh/Compute/Terminal.lean` | The last-column test and the terminal enumeration of `sec:finite` (computational definitions) |
| `KimKimOh/TermCover.lean` | The last-column test: classes, tables and options (`sec:finite`) |
| `KimKimOh/TermLifts.lean` | The terminal enumeration and its witnesses (`sec:finite`, `app:bounded`) |
| `KimKimOh/Normalize.lean` | Normalizing the signs of the last column (`app:bounded`) |
| `KimKimOh/TermBatches.lean` | Assembling the batch checks of the last-column test |
| `KimKimOh/MinTwoOfChecks.lean` | The finite part of §4 from its checks |
| `KimKimOh/ListAll.lean` | Conjunctions over a list |
| `KimKimOh/Compute/Dispatch.lean` | The dispatcher by ranges of `a` (computational definitions) |
| `KimKimOh/DispatchRanges.lean` | The dispatcher from its ranges |

## Generated kernel checks of the finite part

`FirstPassChecks/` is written by `scripts/firstpass/gen_enum.py` from the lists that the Lean programs `scripts/firstpass/Heavy.lean` and `RegionEval.lean` compute; `Terminal/` is written by `scripts/terminal/gen_terminal.py` from the supplement's records.

| Module | Contents |
| --- | --- |
| `KimKimOh/FirstPassChecks/Data3.lean` | The pairs `(a, t)` enumerated for K3 and the blocks left by the whole-block test (generated) |
| `KimKimOh/FirstPassChecks/Dispatch3_0.lean` … `_4` | The dispatcher checks for K3 by ranges of `a` (generated) (5 modules) |
| `KimKimOh/FirstPassChecks/Enum3_0.lean` … `_1` | First-pass enumeration checks for K3 (generated) (2 modules) |
| `KimKimOh/FirstPassChecks/All3.lean` | All first-pass enumeration checks for K3 (generated) |
| `KimKimOh/FirstPassChecks/Data9.lean` | The pairs `(a, t)` enumerated for K9 and the blocks left by the whole-block test (generated) |
| `KimKimOh/FirstPassChecks/Dispatch9_0.lean` … `_6` | The dispatcher checks for K9 by ranges of `a` (generated) (7 modules) |
| `KimKimOh/FirstPassChecks/Enum9_0.lean` … `_20` | First-pass enumeration checks for K9 (generated) (21 modules) |
| `KimKimOh/FirstPassChecks/All9.lean` | All first-pass enumeration checks for K9 (generated) |
| `KimKimOh/Terminal/Blocks3.lean` | The blocks of the last-column test for K3 and their batches (generated) |
| `KimKimOh/Terminal/Batches3_0.lean` … `_22` | Certificates and checks of the last-column test for K3 (generated) (23 modules) |
| `KimKimOh/Terminal/All3.lean` | All batches of the last-column test for K3 (generated) |
| `KimKimOh/Terminal/Blocks9.lean` | The blocks of the last-column test for K9 and their batches (generated) |
| `KimKimOh/Terminal/Batches9_0.lean` … `_19` | Certificates and checks of the last-column test for K9 (generated) (20 modules) |
| `KimKimOh/Terminal/All9.lean` | All batches of the last-column test for K9 (generated) |
| `KimKimOh/Terminal/TabCheck.lean` | Kernel checks of the tables of the last-column test (generated) |

# Correspondence with the manuscript

The Lean follows the manuscript *Completing the Kim–Kim–Oh classification of minimal-rank
`n`-universal lattices for 2 ≤ n ≤ 8* and its computational supplement. In the release, the supplement is in `python/`.
Paths to Lean modules and generators in this guide are relative to `lean/`.
The generators in `scripts/` read the supplement's certificates and reproduce the
committed Lean data byte for byte (`scripts/README.md`).

Labels are the manuscript's `\label`s; numbers are the manuscript's (one counter per
section: Theorems 1.1–1.2, Lemmas 2.1–2.2, Lemma 3.1, Certificates 4.1–4.3, Proposition 5.1,
Lemma A.1; Tables 1–4). The docstrings cite both. The paper indexes the primes from 5 as
`q_1 = 5, q_2 = 7, …`; the Lean's `q i` is the paper's `q_{i+1}`, and `P t` is `P_t`.

**Notation.** The manuscript's last column `(r₁, r₂, f)` is `(d, e, f)` in the Lean. `[G]_p` is the
residue `(a, b, c, d, e, f)` modulo `(8, 4, 8, 4, 4, 8)` at 2 (`r8`, `r4`) or modulo 9 at 3 (`r9`).
Membership in `ℛ_{j,p}` is `accepted2`, `accepted3`; `𝒰_{j,p}(σ)` (the columns modulo `p` all of
whose lifts are accepted) is `perm2`, `perm3`. A profile (`app:prescriptions`) is a list of pairs
`(h, m)` for each `x mod p`, the manuscript's local moduli `(h_p, m_p)`. The Lean calls them
*steps*. `pairsOK` (Certificate 4.1) combines the choices at 2 and 3 into the common
differences `h`, `m`. The manuscript's decomposition `L = K_j ⊥ ℤv` with `Q(v) = s` is described
by a `HostSpec` (`HighBound.lean`), which packages `K`, `j`, `s` and the local tables at 2 and 3;
`H.Target L` says that `L` represents `K ⊥ ⟨s⟩`. The ternary lattice `Λ` to be embedded is `S`
(Gram matrix `G`). In the last-column test, `R_B(r)` is `rDE`, `D₀` is `dZero`,
and `U(B)` is the bound `U` of a `TermCert`. The quinary lattice `Λ₁₁₇` of `prop:exception` is
`quinaryT`.

## Map

| Manuscript | Lean |
| --- | --- |
| Theorem 1.2 (`thm:main`) | `MainTheorem` (`Statement.lean`); `mainTheorem` (`Main.lean`), from `mainTheorem_of_minTwo` (`Assembly.lean`) |
| Theorem 1.1, the two cases used (`thm:kko`) | `kko112_universal` (`Genus/Kko112.lean`), `kko113_universal` (`Genus/Kko113.lean`); used for minimum one in `Assembly.lean` |
| Lemma 2.1(a) (`lem:functional`) | `represents_of_corr` (`Correction.lean`), which rebuilds the embedding of `S` into `L` from a representation of `C` by `K_j`, with `localGlobal_K3`, `localGlobal_K9` (`Bridge/LocalGlobal.lean`, from `rep_g3`, `rep_g9` in `Genus/K3K9.lean`) |
| Lemma 2.1(b), `p ≥ 5` (rank at least 2, or a diagonal entry in `j(𝔽_p^×)²`) | `rank_K3`, `rank_K9`, `square_K3`, `square_K9` (`Local/LargePrimes.lean`) |
| Lemma 2.2 (`lem:local-precision`) and the tests at 2 and 3 | `Local/Precision.lean`, `Local/Hensel.lean`, `Local/Diagonal.lean`; tables `Tables/Accept*.lean`, `Tables/Check*.lean`; `local2_K3`, `local3_K3`, `local2_K9`, `local3_K9` (`Tables/Soundness.lean`) |
| maximality modulo `p` (`eq:maximal`) | `nonzeroMod_of_isMaximal`, `not_four_dvd_det_of_isMaximal` (`MaximalMod.lean`); `nonmax3_false`, `det4_ne_zero` (`Tables/Profiles*.lean`) |
| reduced bases (`finite:geometry`, `eq:lengths`) | `Tern.IsReduced` (`Ternary.lean`); `exists_maximal_reduced` (`Overlattice.lean`, `Reduced.lean`) |
| `eq:highcost`, `eq:sectionbound` | `corr_pos_of_adjForm`, `exists_window` (`Correction.lean`) |
| `eq:shared-prime` | `a_mul_corrDelta` (`Choice.lean`) |
| Lemma 3.1 (`lem:scalar-slice`) | `scalar_slice`, `scalar_slice_one` (`ScalarSlice.lean`); `atMostClasses_weight_not_okAt` (`FirstPass.lean`) |
| §4.1 (`sec:high`), `H_j(a, t)` | `atMostClasses_one_not_okAt` (`Choice.lean`); `Windows.ap_sieve`; `represents_of_high_lt`, `high` (`HighBound.lean`, `Compute/HighBound.lean`) |
| `eq:choices-23` | `perm2`, `perm3` and the profile steps (`Tables/Profiles*.lean`); `atMostClasses_one_not_okAt` (`Choice.lean`) |
| Certificate 4.1 (`cert:progressions`) | `RegionData.hpairs`, checked by `pairs_3`, `pairs_9` (`HostDataChecks.lean`) for `2 ≤ a ≤ 84`; `validOpts_big`, `a0Of_spec` for `a ≥ 73` |
| Certificate 4.2 (`cert:ranges`) | the lists `heavy3`, `heavy9` (536 and 1,136 pairs, largest `a` 494 and 855) with `dispatchOK` (`FirstPassChecks/Dispatch*`, `All*`) |
| the region of blocks left by §4.1 | `region_cover` (`RegionCover.lean`), `hiTab` (`Region.lean`, `Compute/Region.lean`) |
| `eq:block-23` | the progressions `h2`, `h3` of `block_rep_core` (`FirstPass.lean`); the step tables `tableOK2`, `tableOK3` (`Compute/Pass.lean`) |
| whole-block test (`eq:whole-block`) | `block_rep_core`, `block_rep` (`FirstPass.lean`); `blockOK` (`Compute/Pass.lean`); `blockOK_sound` (`PassCheck.lean`) |
| Lemma A.1 (`lem:window`) | `sum_le_ubound` (`WindowBound.lean`), `fastG_spec` (`PassCheck.lean`) |
| enumeration of the region | `enumOK`, `dispatchOK` (`Compute/Enum.lean`); `enumOK_sound` (`Enum.lean`); `FirstPassChecks/` |
| last-column residues | `optOK`, `optCover`, `termOK` (`Compute/Terminal.lean`); `optOK_facts`, `rep_of_optCover` (`TermCover.lean`) |
| enumeration up to `U(B)` and witnesses | `liftsOf`, `witOK` (`Compute/Terminal.lean`); `mem_liftsOf`, `rep_of_witOK`, `termOK_sound` (`TermLifts.lean`); `exists_normal` (`Normalize.lean`); `Terminal/` |
| Certificate 4.3(a) (`cert:finite`), the whole-block test | `enumOK` (`FirstPassChecks/`) |
| Certificate 4.3(b), last-column bounds | `optOK`, `optCover` and the bound part of `termOK` (`Terminal/`) |
| Certificate 4.3(c), bounded matrices and witnesses | `liftsOf`, `witOK` in `termOK` (`Terminal/`) |
| §4 assembled | `minTwo_of_checks` (`MinTwoOfChecks.lean`); `host3`, `host9` (`HostData.lean`); `minTwo6`, `minTwo9` (`Main.lean`) |
| Proposition 5.1 (`prop:exception`) | `not_isUniversal_I6A2` (`Quinary.lean`, `Quinary/Core.lean`) |
| `app:correction-tests` | `Tables/Accept*.lean`, `Tables/Check*.lean`, `Tables/Soundness.lean` |
| `app:prescriptions` | profiles and step tables: `profChunkOK2`, `profChunkOK3`, `chunk2_spec`, `chunk3_spec` (`Tables/Profiles*.lean`); `Tables/ProfCheck*.lean` |
| `app:bounded` | `Compute/Terminal.lean`, `Terminal/` |

## Departures from the manuscript

None changes a statement, a count or a constant of the manuscript. The kernel checks prove what
the proof needs: every pair `(a, t)` that can contain a block of the region is listed
(`dispatchOK`), every block of the region passes the whole-block test or is listed (`enumOK`), and
every listed block passes the last-column test (`termOK`). They do not show that the lists are
minimal: an extra entry would pass them too. The lists agree with the manuscript's counts, the
deferred blocks (836 and 5,147), the retained blocks (99 and 162) and the tested matrices (10,905
and 7,556): the first pass enumerates them (`scripts/firstpass/`), and `gen_terminal.py` matches
every listed block and every tested matrix with the supplement's records.

1. **Options of the last-column test.** The manuscript tries every pair `(x, y)` with
   `B - s ααᵀ > 0`. The certificate lists a subset, chosen by the generator so that the classes
   bounded below `D₀` and the bound `U(B)` are those of all pairs (the supplement's
   `certificates/last_column_bounds.json.gz`). Each listed option carries the prime factors `p ≥ 5` of `Δ` (checked by stripping them from `Δ`,
   primality by trial division) and, for each omitted prime, a square root `w` with
   `B'ᵢᵢ ≡ j w² (mod p)`.
2. **Classes at 3.** A last-column class with no maximal lift modulo 9 is left out of the domain
   of the block. The manuscript keeps it in its coarse count but no maximal lattice has it, so the
   enumerated matrices are the same.
3. **Witnesses.** The manuscript's certificates give a 5×3 matrix `X` with `Xᵀ J X ≡ C`
   (or `≡ C'` for an overlattice). Lean tests `C`, or `C'`, against the acceptance tables at 2
   and 3, which are exactly the residues of such `X` (`app:correction-tests`), and transfers the
   representation of `C'` to `C = Mᵀ C' M` (`enlarge_eq`, `locRep_conj`).
4. **Signs.** The enumeration normalizes `d ≥ 0`, `e ≥ 0` if `d = 0`, and `a e ≥ b d` if `b = 0`
   or `2 b = a`. Lean proves this normalization (`exists_normal`): negate `e₃`, then negate `e₂`
   if `b = 0` or replace `e₂` by `e₁ - e₂` if `2 b = a`.
5. **Whole-block windows.** The window `g` of `eq:whole-block` is found by a fixed-point
   iteration with at most 16 steps (`winIter`). It certifies exactly the blocks of Certificate 4.3(a).
6. **Primitive representations.** Lemma 2.2 gives a primitive representation over `ℤ_p`. The Lean
   proves representation (`LocallyRepresents`: solvability of `Xᵀ K X ≡ C` modulo every `pᵏ`),
   which is what Lemma 2.1 uses.

## Kernel checks

All are `decide +kernel` on definitions in `KimKimOh/Compute/` and generated data; no
`native_decide`.

| Check | Files | What it checks |
| --- | --- | --- |
| acceptance tables | `Tables/Check*.lean` | every chunk of the tables at 2 and 3 carries its witnesses, so every accepted entry is represented over `ℤ₂` or `ℤ₃` (`sound2`, `sound3`) |
| profiles and steps | `Tables/ProfCheck*.lean` | `profChunkOK2`, `profChunkOK3` on every chunk |
| instance data | `HostDataChecks.lean` | step tables, profile masks, valid options for `2 ≤ a₀ ≤ 84` |
| first pass | `FirstPassChecks/Enum*.lean` | `enumOK` for every enumerated `(a, t)` |
| dispatcher | `FirstPassChecks/Dispatch*.lean` | every `(a, t)` that may hold a block of the region is enumerated (`dispatchRange`, by ranges of 40 values of `a`) |
| tables of the last-column test | `Terminal/TabCheck.lean` | `r2OK`, `mxRange` |
| last-column test | `Terminal/Batches*.lean` | `termOK` for every leftover block, in batches |

`FirstPassChecks/All*.lean` and `Terminal/All*.lean` assemble the checks without new kernel
computations beyond the coverage of the batches (`termAll_of_batches`, `dispatchOK_of_ranges`).

The kernel evaluates only definitions in `KimKimOh/Compute/`. Their loops use the recursors
directly (`Compute/Loops.lean`, specified in `Loops.lean`), and the first-pass test has a copy
written with raw `Nat` operations (`blockOKRaw`, equal to `blockOK` by `rfl`), which the kernel
evaluates faster. Each certificate of the last-column test is a `TermCert` (the bound `U`, the
packed options and the packed witnesses); `gen_terminal.py` prints the block and the counts in a
comment above each.

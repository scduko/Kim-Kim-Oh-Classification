# Verification status

## What is proven

The main theorem, in `KimKimOh/Main.lean`, is

```lean
theorem mainTheorem : MainTheorem
```

where (`KimKimOh/Statement.lean`)

```lean
def MainTheorem : Prop :=
  L6.IsUniversal 3 ∧ L9.IsUniversal 3 ∧ ¬ I6A2.IsUniversal 5
```

with `L6 = I₃ ⊥ A₁ ⊥ A₂`, `L9 = I₃ ⊥ A₂ ⊥ ⟨3⟩` and `I6A2 = I₆ ⊥ A₂` (`KimKimOh/Lattices.lean`). A
`GramLattice ι` is an integer matrix indexed by a finite type that is positive definite as a real
matrix; `L.Represents S` means `Xᵀ G_L X = G_S` for an integer matrix `X`; and
`L.IsUniversal n` means that `L` represents every `GramLattice (Fin m)` with `m ≤ n`
(`KimKimOh/GramLattice.lean`). This is Theorem 1.2 of the manuscript.

The theorem has no hypotheses. The classical results that the manuscript cites for it, the
global part of Lemma 2.1 and the two cases of Theorem 1.1 it uses, are proved here
(`localGlobal_K3`, `localGlobal_K9`, `kko112_universal`, `kko113_universal`), from the genus
representation theorem and the Conway–Sloane mass formula of the vendored QuadFormsKB
(`docs/PROVENANCE.md`).

## How it is checked

**Full local verification.** Run the Lean and generator commands from `lean/` and the Python certificate checker from `python/`. Both directories are at the repository root.

1. **Build.** `lake build` compiles the root module `KimKimOh` and every module it imports: the
   modules of `KimKimOh/` and their dependencies in `QuadFormsKB/`, with warnings treated as
   errors in `KimKimOh/`.
2. **Axiom audit.** `lake env lean scripts/CheckAxiomsMain.lean` fails unless `mainTheorem` and
   the main intermediate theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
3. **Kernel replay.** `python3 scripts/full_build.py replay K`, for `K` from 0 to 4, has the Lean
   kernel check the declarations of every compiled `KimKimOh` module again, independently of the
   elaborator: for each module it runs `lake env lean --run scripts/ReplayModule.lean <module>`,
   which replays the module's declarations in the environment of its imports.
   `lake env leanchecker KimKimOh` does the same for all modules in one process; in the clean-room
   verification it stopped with a segmentation fault (Verification record).
4. **The supplement.** In `python/`,
   `python3 verify_ternary_certificates.py --workers 4` reproduces
   `expected_output/certificate_verification.txt`.
5. **The generators.** Each generator of `scripts/` reproduces the committed Lean data byte for
   byte (`scripts/README.md`), including the first-pass lists written by
   `scripts/firstpass/Heavy.lean` and `RegionEval.lean`.

**By the workflows.** `.github/workflows/supplement.yml` runs on pull requests and pushes to
`main` that change the supplement, the scripts or the Lean data read from the supplement. It runs
the certificate checker against `expected_output/certificate_verification.txt` and checks that
`gen_profiles.py`, `gen_chunkdata.py` and `gen_terminal.py` reproduce the committed Lean files.
`.github/workflows/full.yml`, started by hand, runs the full verification above (the build with
the kernel checks of §4, `scripts/CheckAxiomsMain.lean` and kernel replay) on GitHub's
runners: a hosted job has at most 6 hours, so it chains jobs, the heavy modules in four parts of
about equal cost (`scripts/full_build.py`), each passing the build on to the next.
Five parallel jobs then replay the project modules. Each job passes the exact names of its
assigned modules to `scripts/ReplayModule.lean`, which replays their declarations from their
imports using the same kernel operation as the local `leanchecker` command.
`.github/workflows/lean.yml` runs on pull requests and pushes to `main` that change files outside
the supplement and documentation. It rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` and `@[extern]`
in the sources, builds the modules that do not depend on a generated kernel check of §4
(`scripts/ci_modules.py`) with the QuadFormsKB modules they import, and runs
`scripts/CheckAxioms.lean`, the axiom audit of their main theorems. The kernel checks of §4 take
several CPU-hours, so it leaves them to `full.yml`.

The axiom audit is what excludes `sorry`, `admit`, added axioms and `native_decide`: each would
appear as an axiom outside the allowlist. The finite computations are propositions proved by
`decide +kernel` on definitions in `KimKimOh/Compute/`, which the kernel evaluates, so they add no
trust beyond the kernel. Some raise `maxRecDepth` or the heartbeat limit; these options affect
elaboration only. `docs/PAPER_CORRESPONDENCE.md` lists the checks.

## Verification record

**Clean-room verification, November 22, 2026.** The staged tree at `5455e46` of the working
repository was cloned into an empty directory and checked on a machine with 4 cores and 15 GB of
memory. The 200 project modules, the vendored QuadFormsKB sources, the pinned build configuration,
the axiom audits, and the Python verification programs, certificates and expected output
match that revision byte for byte under their new paths. The generator instructions use the new layout. The per-module replay driver used for the checks is included
in the release. The Mathlib cache host was not reachable from that machine, so
`.lake/packages` was linked to a local build of the pinned revisions (Mathlib `fc4f59e`, as in
`lake-manifest.json`). Everything in this repository, including the vendored QuadFormsKB, was built
from scratch.

| Check | Result |
| --- | --- |
| Build of QuadFormsKB and the 93 light modules (`scripts/ci_modules.py`) | Passed: 12,535 jobs, 1 h 23 min, 5.2 CPU-hours, at most 8.0 GB. |
| Build of the 107 other modules, one `lake build` each, at most two at a time, `LEAN_NUM_THREADS=2` | All passed: 4.7 CPU-hours, at most 9.1 GB (`KimKimOh.FirstPassChecks.Enum9_11`). The times are in `scripts/module_costs.json`. |
| `lake build` | Passed: nothing left to build (12,750 jobs). |
| `scripts/CheckAxioms.lean`, `scripts/CheckAxiomsMain.lean` | Passed: each of the 42 and 15 listed theorems, `mainTheorem` among them, depends on exactly `propext`, `Classical.choice` and `Quot.sound`. |
| Kernel replay, `scripts/ReplayModule.lean` once per module, at most two at a time | All 200 modules replayed, in 4.9 hours summed over the modules, at most 7.6 GB. |
| `lake env leanchecker KimKimOh` | Stopped by a segmentation fault (exit code 139) after 29 s, at 10.4 GB. The replay by module above replaces it. |
| `verify_ternary_certificates.py --workers 4` in `python/` | Passed: the output is identical to `expected_output/certificate_verification.txt`. |
| `scripts/firstpass/Heavy.lean` and `RegionEval.lean`, for 3 and 9 | Passed: the regenerated `heavy{3,9}.txt` and `left{3,9}.txt` of `scripts/firstpass/data/` are identical to the committed files. The region has 534,827 blocks for L₆ and 8,521,181 for L₉ (Table 4), of which 836 and 5,147 fail the whole-block test. `RegionEval.lean 9` took 2 h 45 min. |
| Every generator of `scripts/`, with the commands of `scripts/README.md`, run on a copy of the tree | Passed: every regenerated file is identical to the committed one. The terminal generator used all 18,461 witnesses. |

On November 22, 2026, the following checks of the updated supplement were run against the staged
Lean sources at `1449f5a`.

| Check | Result |
| --- | --- |
| Python search and certificate checker | Both standard-output transcripts matched the files in `expected_output/` byte for byte. The checker verified all 10,905 witnesses for L₆ and all 7,556 for L₉. |
| Supplement-dependent Lean generators | `gen_profiles.py`, `gen_chunkdata.py` and `gen_terminal.py` reproduced all 51 of their committed Lean files byte for byte. The terminal generator used every witness. |

The kernel checks prove that every block of the region passes the whole-block test or is listed,
and that every listed block passes the last-column test, with a witness for each matrix it leaves.
The lists agree with the manuscript's counts: 836 blocks for `L₆` and 5,147 for `L₉` fail the
whole-block test, 99 and 162 need an enumeration, and 10,905 and 7,556 matrices are tested. This
census comes from the first-pass enumeration and from matching the supplement's records
(`docs/PAPER_CORRESPONDENCE.md`).

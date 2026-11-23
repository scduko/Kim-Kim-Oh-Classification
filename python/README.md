# Ternary universality in the Kim–Kim–Oh classification

This computational supplement reproduces Certificates 4.1–4.3 of [Scott Duke Kominers’s manuscript](../README.md). The certificates are used in the proof that $L_6$ and $L_9$ represent every positive-definite integral ternary lattice. The search and the checker use exact integer arithmetic, including exact fractions for the rational bounds. Run the commands below from the directory containing this README with Python 3.10 or later. Both print to standard output. The files in `expected_output/` give the reference transcripts for comparison.

| Task | Command | Expected output |
| --- | --- | --- |
| Reproduce the search | `python3 reproduce_ternary_search.py --workers 4` | `expected_output/ternary_search.txt` |
| Check the supplied certificates | `python3 verify_ternary_certificates.py --workers 4` | `expected_output/certificate_verification.txt` |

## Guide to the appendix

| Manuscript | Computation | Python source or supplied records |
| --- | --- | --- |
| Appendix A.1, Table 3 | Primitive local representations and coefficient classes at 2 and 3 | `verification/local_representation.py`, `verification/residue_census.py` |
| Appendix A.2, Certificates 4.1 and 4.2 | Arithmetic progression steps and determinant intervals | `verification/scalar_sieve.py`, `audit/verify_steps_and_ranges.py`, `certificates/local_progression_steps.tsv` |
| Appendix A.3, Certificate 4.3(a) and (b) | Common pairs for binary blocks and determinant bounds by last-column class | `audit/verify_block_coverage.py`, `certificates/binary_block_pairs.json.gz`, `certificates/last_column_bounds.json.gz` |
| Appendix A.3, Certificate 4.3(c) | Bounded ternary Gram matrices and their representation witnesses | `audit/verify_representation_witnesses.py`, `certificates/bounded_gram_matrices.txt.gz`, `certificates/representation_witnesses.jsonl.gz` |
| Appendix B | Lean theorem, arithmetic inputs, and kernel checks corresponding to the Python certificates | Manuscript correspondence and build commands under “Lean formalization” below |

## Matrices and congruences

Let $\Lambda$ be the ternary lattice to be represented and let $G$ be its Gram matrix in a fixed basis. The programs store $G$ as `(a,b,c,d,e,f)`, with rows $(a,b,d)$, $(b,c,e)$, and $(d,e,f)$. Thus the leading binary block $B$ has entries $(a,b,c)$, and $(d,e)$ are the manuscript's $(r_1,r_2)$.

We seek an isometric embedding $\Lambda\hookrightarrow L$ for each $L\in\{L_6,L_9\}$. Fix $L$ and write $L=L(j,s)=K_j\perp\mathbb Z v$, where $v$ generates the rank-one summand and has norm $s$. The two choices are $L(3,2)=L_6$ and $L(9,1)=L_9$. The column $\lambda=(x,y,k)^{\mathsf T}$ gives the coefficients of the three basis images along $v$. Their components in $K_j$ must therefore have Gram matrix $C=G-s\lambda\lambda^{\mathsf T}$.

For $p=2,3$, the notation $[G]_p$ denotes the entrywise congruence class in the fixed basis. At $2$ the diagonal entries are taken modulo $8$ and the off-diagonal entries modulo $4$. At $3$ all six entries are taken modulo $9$. Membership of $[C]_p$ in $\mathcal R_{j,p}$ certifies that $K_j$ represents $C$ over $\mathbb Z_p$. The set $\mathcal U_{j,p}([G]_p)$ consists of the triples modulo $p$ for which every integral lift $\lambda$ gives $[C]_p\in\mathcal R_{j,p}$.

### Code and manuscript notation

| Python | Manuscript |
| --- | --- |
| `target`, `host`, `scale` | `target` is $\det L$, equal to $6$ for $L_6$ and $9$ for $L_9$. The map `TARGET_HOSTS` in `verification/notation.py` takes this integer to $(j,s)$, where `host` is $j=\det K_j$ and `scale` is $s=Q(v)$. |
| `delta`, `Delta` | $\delta=\det B$, $\Delta=\det B'$ with $B'=B-s\alpha\alpha^{\mathsf T}$ |
| `D0`, `block_form` | $D_0=\lceil3\delta^2/(4a)\rceil$, $R_B(r)=cr_1^2-2br_1r_2+ar_2^2$ |
| `uniform_gap_bound(t)`, `uniform_gap_bounds()` | $g_t$ in Section 4.1 and Appendix A.2, computed by the search and the checker, respectively |
| `weighted_gap_bound` | The bound $g$ for a specified list of primes and weights in the last-column test |
| `local_triples`, `scalar_cost` | The choices $(x,h,m)$ and the right-hand side of the inequality for $\beta$ in Section 4.1 |
| `uniform_beta_bound` | $H_j(a,t)$ in Certificate 4.2 |
| `block_delta_bound`, `checked_block_delta_bound` | The search and checker values of $\lfloor aH_j(B,t)\rfloor$ |
| `upper_det` | The integer upper bound on $D$ for a class, or $U(B)$ after taking the maximum over the surviving classes |
| `m2`, `m3`, `scaled_gap_squared` | The two local steps for $k$, and $sg^2$ in the bound $\lfloor\delta^2 sg^2(m_2m_3)^2/(4\Delta)\rfloor$ |

## Certificates 4.1 and 4.2 — coefficient choices and determinant ranges

Run `python3 audit/verify_steps_and_ranges.py --verify-tables`. Using the diagonal matrices in Table 1, `verification/local_representation.py` constructs the sets $\mathcal R_{j,p}$ by adding the rows of a potential embedding matrix one at a time. The table builder, witness generator and witness checker all use the diagonal order in Table 1. The table builder retains the congruence class of the partial Gram matrix and the span of these rows modulo $p$. The rank condition in Lemma 2.2 requires that the five rows span $\mathbb F_p^3$. To recognize a maximal ternary lattice locally, it tests whether $4\nmid\det G$ at $2$ and whether an integral overlattice of index $3$ exists at $3$. The coefficient tests in `verification/residue_census.py` use all lifts specified above.

For each maximal Gram matrix class and each $x\bmod p$, the certificate records the possible pairs of local moduli $(h_p,m_p)$ for $y$ and $k$. Each modulus is $1$ (all residues modulo $p$) or $p$ (one chosen residue). The residue for $k$ may depend on $y$. Combining the choices at $2$ and $3$ gives the common differences $h=h_2h_3$ and $m=m_2m_3$ in the progressions $y_0+h\mathbb Z$ and $k_0(y)+m\mathbb Z$. Each list retains the minimal pairs under coordinatewise divisibility. The field `steps_by_x` in `certificates/local_progression_steps.tsv` holds these lists indexed by $x\bmod p$. The certificate calls this collection a *profile*. The other fields give $j$ (`host_determinant`), the prime, the first diagonal entry modulo $8$ or $9$, and the number of maximal classes with these data.

The checker reconstructs these records. For a given first diagonal entry $a$, it combines the lists at $2$ and $3$ and checks that every required pair has a choice of $(x,h,m)$ passing the size and signed-divisor tests of Section 4.1. For each pair it minimizes the upper bound in Section 4.1 over its available choices, then takes the largest of these minima. From this bound it reconstructs the intervals for $\delta=\det B$ and compares them with the intervals used in the search. Running the same command without `--verify-tables` computes the cutoffs from the supplied TSV.

In the search, `verification/scalar_sieve.py` assigns $t$ by $P_t\le\delta<P_{t+1}$, where $P_t$ is the product of the first $t$ primes at least $5$. This bounds the number of primes to consider when choosing $y$ and then $k$. It checks the initial inequality for the argument excluding $t\ge27$ and calculates the finite intervals for $t<27$.

## Certificate 4.3(a) and (b) — binary blocks and last columns

Run `python3 audit/verify_block_coverage.py --workers 4`. For each block $B$, `verification/block_filter.py` restricts the two lists of local classes to those with the given leading block before computing $H_j(B,t)$. It seeks one pair $(x,y)$ such that every maximal ternary lattice with that block in a reduced basis admits a $k$ making $C_G(\lambda)$ positive definite and represented by $K_{j,p}$ at every prime. The progression for $k$ has a common step, while its starting class may depend on the remaining Gram entries.

Each record in `certificates/binary_block_pairs.json.gz` has the form `[target,a,t,codes]`, where `target` is $\det L$ and `codes` is a base64 string. In ascending $(b,c)$ order there is one byte per block passing the filter $\delta\le aH_j(B,t)$ in the region of Section 4.2. Direction codes lie between $0$ and $90$. The reserved value $255$ indicates that the search found no such pair for the whole block. For these blocks the last-column test bounds $D$ for a possible exception separately in each class $(r_1,r_2,f)\bmod24$. Each other byte encodes the chosen pair as $13x+y+6$. The checker recovers the local steps, checks the determinant inequality and counts the prime exclusions, including a check with all prime factors. For a block sent to the last-column test it verifies that every allowed pair fails the sufficient test of Appendix A.3.

The sign conditions on the reduced basis are imposed before fixing a last-column class. For each remaining block, `verification/bounded_exact.py` factors the determinant of the leading block of $C$ and bounds $D=\det G$ for each allowed last-column class modulo $24$. Each record in `certificates/last_column_bounds.json.gz` is `[target,a,b,c,U,bitmap]`. In the hexadecimal bitmap, bit `(12*d+e)*24+f` records a surviving class, with $d,e$ taken modulo $12$ and $f$ modulo $24$. Each bit represents four triples modulo $24$. The replay indexes the same bits by the class at $3$ first, then the class at $2$, as documented in `reader_bits`. For blocks without a record the checker verifies that every candidate class has an upper bound below the reduction bound $D_0$. For each listed block it verifies the surviving classes and their common upper bound $U(B)$, the maximum of their individual least integer bounds. The pair and progression may depend on the last-column class. At $2$ and $3$ that progression must work for all compatible local classes maximal at those primes. The checker counts the classes admitting a maximal lift modulo $9$, enumerates the bounded integral matrices, and compares the sorted list left after the maximality-at-$3$ and coprimality tests with `certificates/bounded_gram_matrices.txt.gz`.

The checker reproduces the counts in Table 4 of the manuscript.

| Count | $L_6$ | $L_9$ |
| --- | ---: | ---: |
| Binary blocks in the region for $H_j(B,t)$ | 534,827 | 8,521,181 |
| Blocks with $D$ bounded by last-column class | 836 | 5,147 |
| Blocks with a last-column class of bound $\ge D_0$ | 99 | 162 |
| Bounded integral lifts in the surviving classes | 29,831 | 10,407 |
| Gram matrices tested individually | 10,905 | 7,556 |

For $L_9$ the seven blocks $(a,b,c)$ passed to the last-column test at $t=5$ are $(350,175,525)$, $(357,126,357)$, $(357,153,357)$, $(390,65,585)$, $(550,165,605)$, $(585,130,585)$ and $(585,260,585)$. For $L_6$, one pair suffices for every block at $t=5$.

To apply the last-column test directly to every block in the uniform ranges of Section 4.1, run `python3 reproduce_ternary_search.py --all-blocks --workers 4`. The expected output is in `expected_output/all_blocks_search.txt`.

## Certificate 4.3(c) — a representation for each remaining matrix

Run `python3 audit/verify_representation_witnesses.py`. The search in `verification/terminal_corrections.py` chooses $\lambda$ from $\{-2,-1,0,1,2\}^3$ in order of increasing maximum absolute entry. Ties are broken by the sum of the absolute entries and then by lexicographic order, fixing the recorded witness. The checker reads one record per matrix $G$ from `certificates/representation_witnesses.jsonl.gz`, in the order of `certificates/bounded_gram_matrices.txt.gz`. Each line has the form `[key,lambda,[z2,X2],[z3,X3]]`, where `key=[target,a,b,c,d,e,f]`.

The checker forms $C$, checks that it is positive definite, and verifies the following conditions.

- For $p=2,3$, let $J$ be the diagonal Gram matrix of $K_j$ in Table 1. If the stored value for $z_p$ is `null`, set $F=C$. Otherwise replace the basis vector at the first nonzero coordinate of $z_p$ by $z_p/p$. That coordinate equals $1$. Check that the new Gram matrix $F$ is integral. In both cases check that $X_p$ has rank $3$ modulo $p$ and $[X_p^{\mathsf T}JX_p]_p=[F]_p$. Its five rows are in the order of the entries of $J$. A representation of the index-$p$ overlattice restricts to one of $C$.
- At each prime $p\ge5$ dividing the gcd of the $2\times2$ minors of $C$, check that some diagonal entry modulo $p$ belongs to $j(\mathbb F_p^\times)^2$. At every other prime $p\ge5$, $C$ has rank at least $2$ modulo $p$.

These checks verify each prescribed representation using the stored matrices and local congruences.

## What the Python programs share

The search and the coverage checker both use the representation table and maximality flags in `verification/local_representation.py`, the sets returned by `residue_census.permissible`, and the intervals returned by `scalar_sieve.ranges`. They also use the same map from $\det L$ to $(j,s)$ and the same direction-byte format. The coverage checker reconstructs the whole-block witnesses, last-column bounds and integral lifts with its own routines.

The `--verify-tables` option in `audit/verify_steps_and_ranges.py` starts from the shared representation tables and maximality flags. It checks the four representation counts and the two counts of Gram classes of maximal ternary lattices in Table 3. It independently constructs the permissible columns and compares every entry with `permissible`, reconstructs the profiles and compares them with `local_progression_steps.tsv`, and checks the interval endpoints and their $t$ values against `ranges`. It also checks the 536 and 1,136 nonempty intervals of Certificate 4.2. These comparisons do not independently construct the underlying primitive representation tables.

Within the search, both profile groupings use the same computation of steps for each $x$, and both tests of a single progression use the same least-step routine. The audit recomputes progression steps independently. Its block and last-column tests share a trial-division routine. The search and the standalone witness checker each retain a separate factorization routine. The witness checker verifies the matrices against its own copy of Table 1 and uses the same map from $\det L$ to $(j,s)$.

## Lean formalization

In [Main.lean](../lean/KimKimOh/Main.lean), `KimKimOh.mainTheorem` proves all three assertions of Theorem 1.2. The two binary universality results and the local–global implications for the two quinary lattices are theorems in this development. The [correspondence guide](../lean/docs/PAPER_CORRESPONDENCE.md) maps the manuscript to the Lean proof.

The Lean kernel checks the local tables, the coverage of the binary blocks, the last-column bounds, and the representation witnesses. The terminal-data generator reads the checker interface `audit/check_coverage.py` and the records `audit/coverage.json.gz` and `audit/witnesses.jsonl.gz`. The latter are identical copies of `certificates/last_column_bounds.json.gz` and `certificates/representation_witnesses.jsonl.gz`. Regenerating the default records refreshes both copies. For each terminal witness the Python checker verifies the supplied embedding matrices at 2 and 3. Lean checks the same Gram classes against its verified local tables.

From the repository root, with the pinned toolchain and Mathlib dependencies installed, run

```sh
cd lean
lake build
lake env lean scripts/CheckAxiomsMain.lean
```

The [generator instructions](../lean/scripts/README.md) describe how to reproduce the Lean data. The [verification record](../lean/docs/STATUS.md) identifies which checks have been run.

## Regenerating the records

Run the following commands in order. The second writes the binary-block records, the surviving last-column classes with their bounds, and the list of Gram matrices used by the third.

```sh
python3 audit/verify_steps_and_ranges.py --export
python3 audit/generate_block_records.py --workers 4
python3 audit/generate_representation_witnesses.py
```

# The Kim–Kim–Oh classification

This repository contains the computational supplement and the Lean 4 formalization
accompanying *Completing the Kim–Kim–Oh Classification of Minimal-Rank* $`n`$*-Universal Lattices for* $`2 \le n \le 8`$, by Scott Duke Kominers. **Manuscript link:** TK.

## Results

Theorem 1.2 settles the three cases left open by [Kim, Kim, and Oh (1999)](#reference)
in their classification of minimal-rank $n$-universal lattices for $2 \le n \le 8$. We show that the
lattices $I_3 \perp A_1 \perp A_2$ and $I_3 \perp A_2 \perp \langle 3\rangle$ each
represent every positive-definite integral ternary lattice and thus are $3$-universal.
We show that $I_6 \perp A_2$ is not $5$-universal by exhibiting a positive-definite
integral lattice of rank $5$ that it does not represent.

## Computational supplement

The [computational supplement](python/README.md)
reproduces Certificates 4.1–4.3 of the manuscript, which establish the finite checks
for the two ternary universality assertions. It includes the Python search programs,
the certificate data, and a separate checker that verifies the certificates using
exact arithmetic.

To check the certificates, use Python 3.10 or later and start in the repository root.

```sh
cd python
python3 verify_ternary_certificates.py --workers 4
```

## Lean formalization

The Lean theorem [`KimKimOh.mainTheorem`](lean/KimKimOh/Main.lean) proves
[all three assertions](lean/KimKimOh/Statement.lean) without additional hypotheses.
We are extending the development to a Lean formalization of the full Kim–Kim–Oh
classification.

To build the proof, use the pinned Lean 4.36.0 toolchain and start in the repository root.

```sh
cd lean
lake exe cache get
lake build
```

The [correspondence guide](lean/docs/PAPER_CORRESPONDENCE.md) maps the manuscript to the
Lean proofs. The [verification record](lean/docs/STATUS.md) gives the commands and results
for the certificate checks, axiom audits, and kernel replay. The
[sources](lean/docs/PROVENANCE.md) identify the data and classical results used in the proof.

## Reference

Byeong Moon Kim, Myung-Hwan Kim, and Byeong-Kweon Oh,
[“2-universal positive definite integral quinary quadratic forms”](https://doi.org/10.1090/conm/249/03747),
in *Integral Quadratic Forms and Lattices*, Contemporary Mathematics **249** (1999),
51–62. In Section 6, Proposition 3, parts (1) and (3), the authors mark the three open cases with asterisks.

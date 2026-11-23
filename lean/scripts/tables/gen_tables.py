"""Generate the certified local tables of `app:correction-tests` (KimKimOh/Tables/Data/T*.lean).

Usage: python3 -I gen_tables.py WITDP [OUTDIR]

WITDP is the compiled `witdp.c` (`gcc -O2 -o witdp witdp.c`); OUTDIR defaults to
KimKimOh/Tables/Data.

For each quinary lattice K ∈ {K₃, K₉} and p ∈ {2, 3}, with the diagonal Gram matrix J of
KimKimOh/Local/Diagonal.lean, the accepted residues `ℛ_{j,p}` are the Gram residues of Xᵀ J X for
integer 5 × 3 matrices X whose columns are independent modulo p (entries modulo 9 at 3; diagonal
modulo 8 and off-diagonal modulo 4 at 2). `witdp -a` computes them.

A table is stored by chunks, one for each leading binary block (a, b, c). Within a chunk the
accepted set is a union of orbits of e₃ ↦ ε e₃ + α e₁ + β e₂ (ε = ±1), which fix (a, b, c). For
each orbit we store one witness (X, Y) with Xᵀ Y ≡ 1 (mod p), found by `witdp`; the kernel
regenerates the orbits, checks every witness and checks that the orbits cover the chunk
(`accChunkOK2`, `accChunkOK3`).
"""
import os
import subprocess
import sys
from itertools import combinations, product

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
HOSTS = {  # name: (p, diagonal of J)
    "32": (2, (1, 1, 3, 3, 3)),
    "92": (2, (1, 3, 3, 3, 3)),
    "33": (3, (1, 1, 1, 2, 6)),
    "93": (3, (1, 1, 2, 3, 6)),
}


def moduli(p):
    """The moduli of the residue (a, b, c, d, e, f) of a Gram matrix."""
    return (8, 4, 8, 4, 4, 8) if p == 2 else (9,) * 6


def encode(p, g):
    """The mixed-radix code of a residue, as in `witdp.c`."""
    c = 0
    for v, m in zip(g, moduli(p)):
        c = c * m + v % m
    return c


def decode(p, c):
    g = []
    for m in reversed(moduli(p)):
        g.append(c % m)
        c //= m
    return tuple(reversed(g))


def gram(J, X):
    """The entries (a, b, c, d, e, f) of Xᵀ J X."""
    g = [[sum(J[r] * X[r][i] * X[r][j] for r in range(5)) for j in range(3)] for i in range(3)]
    return (g[0][0], g[0][1], g[1][1], g[0][2], g[1][2], g[2][2])


def residue(p, g):
    return tuple(v % m for v, m in zip(g, moduli(p)))


def act(p, blk, col, al, be, ep):
    """The last column (d, e, f) after e₃ ↦ ε e₃ + α e₁ + β e₂, for the leading block blk."""
    a, b, c = blk
    d, e, f = col
    M = moduli(p)
    return ((ep*d + al*a + be*b) % M[3], (ep*e + al*b + be*c) % M[4],
            (ep*ep*f + al*al*a + be*be*c + 2*al*be*b + 2*ep*al*d + 2*ep*be*e) % M[5])


def group(p):
    """The changes of basis (α, β, ε) acting on a chunk: ε = ±1 modulo 9 or 8."""
    if p == 3:
        return [(al, be, ep) for al in range(9) for be in range(9) for ep in (1, 8)]
    return [(al, be, ep) for al in range(4) for be in range(4) for ep in (1, 7)]


def inv_mod_matrix(M, p):
    """The inverse of a 3 × 3 matrix modulo the prime p, or None."""
    a = [[M[i][j] % p for j in range(3)] + [int(i == j) for j in range(3)] for i in range(3)]
    for col in range(3):
        piv = next((r for r in range(col, 3) if a[r][col]), None)
        if piv is None:
            return None
        a[col], a[piv] = a[piv], a[col]
        inv = pow(a[col][col], -1, p)
        a[col] = [x * inv % p for x in a[col]]
        for r in range(3):
            if r != col and a[r][col]:
                f = a[r][col]
                a[r] = [(x - f * y) % p for x, y in zip(a[r], a[col])]
    return [row[3:] for row in a]


def find_Y(X, p):
    """Y (5 × 3, entries modulo p) with Xᵀ Y ≡ 1 (mod p), supported on three rows of X."""
    for rows in combinations(range(5), 3):
        M = [X[r] for r in rows]                  # Xᵀ Y = Mᵀ Y' for Y' the rows of Y on `rows`
        Minv = inv_mod_matrix(M, p)
        if Minv is None:
            continue
        Yp = [[Minv[j][i] for j in range(3)] for i in range(3)]   # Y' = (Mᵀ)⁻¹ = (M⁻¹)ᵀ
        Y = [[0, 0, 0] for _ in range(5)]
        for t, r in enumerate(rows):
            Y[r] = Yp[t]
        return Y
    return None


def pack(p, X, Y):
    """A witness as one number: the digits of X in base 9 (p = 3) or 4 (p = 2), then those of Y
    in base p, entry (r, c) at digit 3 r + c."""
    bx = 9 if p == 3 else 4
    w = sum(X[r][c] * bx ** (3 * r + c) for r in range(5) for c in range(3))
    w2 = sum(Y[r][c] * p ** (3 * r + c) for r in range(5) for c in range(3))
    return w + bx ** 15 * w2


def accepted_py(p, J):
    """The accepted residues by a plain dynamic program in Python (fast enough at p = 2 only);
    a cross-check of `witdp -a`."""
    per = lambda d: 4 if p == 2 else (3 if d % 3 == 0 else 9)
    M = moduli(p)
    states = {(frozenset([(0, 0, 0)]), (0,) * 6)}
    for d in J:
        new = set()
        for span, g in states:
            for v in product(range(per(d)), repeat=3):
                vm = tuple(x % p for x in v)
                sp = frozenset(tuple((u[i] + t * vm[i]) % p for i in range(3))
                               for u in span for t in range(p))
                con = (d*v[0]*v[0], d*v[0]*v[1], d*v[1]*v[1], d*v[0]*v[2], d*v[1]*v[2], d*v[2]*v[2])
                new.add((sp, tuple((x + y) % m for x, y, m in zip(g, con, M))))
        states = new
    return {g for sp, g in states if len(sp) == p ** 3}


def run_witdp(witdp, p, J, args=(), inp=None):
    return subprocess.run([witdp, str(p)] + [str(d) for d in J] + list(args), input=inp,
                          capture_output=True, text=True, check=True).stdout.split("\n")


def orbit_reps(p, name, chunks):
    """For each chunk, the least element of each orbit; checks that the chunk is invariant."""
    reps = {}
    for blk, pts in chunks.items():
        left, rs = set(pts), []
        while left:
            x = min(left)
            orb = {act(p, blk, x, *gp) for gp in group(p)}
            assert orb <= pts, ("not invariant", name, blk, x)
            left -= orb
            rs.append(x)
        reps[blk] = rs
    return reps


def witnesses(witdp, p, J, name, reps):
    """The packed witnesses (X, Y) of the orbit representatives, by chunk."""
    allreps = [blk + r for blk in sorted(reps) for r in reps[blk]]
    inp = "\n".join(str(encode(p, g)) for g in allreps) + "\n"
    out = run_witdp(witdp, p, J, inp=inp)
    wits = {}
    for g, line in zip(allreps, out):
        assert line != "NONE", (name, g)
        xs = list(map(int, line.split()))
        X = [xs[3 * r:3 * r + 3] for r in range(5)]
        assert residue(p, gram(J, X)) == g, (name, g, X)
        Y = find_Y(X, p)
        assert Y is not None
        for i in range(3):
            for k in range(3):
                assert sum(X[r][i] * Y[r][k] for r in range(5)) % p == int(i == k)
        wits.setdefault(g[:3], []).append(pack(p, X, Y))
    return wits, len(allreps)


def tree(vals, depth, leaf):
    """A complete binary tree (`BT`) of the given depth over the list vals."""
    if depth == 0:
        return leaf(vals[0] if vals else None)
    half = 2 ** (depth - 1)
    return f"(.node {tree(vals[:half], depth - 1, leaf)} {tree(vals[half:], depth - 1, leaf)})"


def write_table(outdir, name, p, acc, chunks, wits, nwits):
    if p == 3:
        nblk, depth = 729, 10
        loc, blkidx = (lambda d, e, f: 81 * d + 9 * e + f), (lambda a, b, c: 81 * a + 9 * b + c)
    else:
        nblk, depth = 256, 8
        loc, blkidx = (lambda d, e, f: 32 * d + 8 * e + f), (lambda a, b, c: 32 * a + 8 * b + c)
    chunkbits = [0] * nblk
    chunkwits = [[] for _ in range(nblk)]
    for blk, pts in chunks.items():
        i = blkidx(*blk)
        for (d, e, f) in pts:
            chunkbits[i] |= 1 << loc(d, e, f)
        chunkwits[i] = sorted(wits[blk])
    acc_tree = tree(chunkbits + [0] * (2 ** depth - nblk), depth,
                    lambda v: f"(.leaf 0x{(v or 0):x})")
    wit_tree = tree(chunkwits + [[]] * (2 ** depth - nblk), depth,
                    lambda v: "(.leaf [" + ", ".join(str(x) for x in (v or [])) + "])")
    host = "K₃" if name[0] == "3" else "K₉"
    with open(os.path.join(outdir, f"T{name}.lean"), "w") as fh:
        fh.write(f"""-- Generated by scripts/tables/gen_tables.py; do not edit.
import KimKimOh.Tables.Bits

/-!
# The local table of {host} at {p} (generated)

`acc{name}`: the accepted Gram residues by chunks ({len(acc)} residues); `wit{name}`: one witness per
orbit in each chunk ({nwits} witnesses).
-/

namespace KimKimOh.Tables

set_option maxRecDepth 100000 in
/-- The accepted residues of {host} at {p}, by chunks. -/
def acc{name} : BT ℕ := {acc_tree}

set_option maxRecDepth 100000 in
/-- The witnesses, by chunks. -/
def wit{name} : BT (List ℕ) := {wit_tree}

end KimKimOh.Tables
""")


def main():
    if len(sys.argv) not in (2, 3):
        raise SystemExit(__doc__)
    witdp = os.path.abspath(sys.argv[1])
    outdir = sys.argv[2] if len(sys.argv) == 3 else os.path.join(ROOT, "KimKimOh/Tables/Data")
    os.makedirs(outdir, exist_ok=True)
    for name, (p, J) in HOSTS.items():
        acc = {decode(p, int(c)) for c in run_witdp(witdp, p, J, args=["-a"]) if c}
        if p == 2:
            assert acc == accepted_py(p, J), name
        chunks = {}
        for g in acc:
            chunks.setdefault(g[:3], set()).add(g[3:])
        reps = orbit_reps(p, name, chunks)
        wits, nwits = witnesses(witdp, p, J, name, reps)
        write_table(outdir, name, p, acc, chunks, wits, nwits)
        print(f"{name}: {len(acc)} accepted, {nwits} witnesses", flush=True)


if __name__ == "__main__":
    main()

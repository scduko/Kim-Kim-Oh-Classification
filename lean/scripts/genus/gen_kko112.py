"""Generate the kernel-checked data for Kim–Kim–Oh's `K₂₂ = ⟨1,1,2⟩ ⊥ A₂` (`kko112`).

Usage: python3 -I gen_kko112.py data > KimKimOh/Genus/Kko112Data.lean
       python3 -I gen_kko112.py hard > KimKimOh/Genus/Kko112HardData.lean

* `w22two`: for each residue class of a binary `C = [[a, b], [b, c]]` modulo `(8, 4, 8)`, either a
  witness `X`, `Y` (5 x 2) with `Xᵀ M X ≡ C` (modulo 8 on the diagonal, 4 off it) and
  `Xᵀ M Y ≡ 1 (mod 2)`, for `M = hostForm 2 2 (-1) 2 = ⟨1, 1, 2⟩ ⊥ A₂` (tag 0), or the direction of
  an integral superlattice of index 2 (tags 1, 2, 3 as in `gen_local_binary.py`).
* `w22three`: for each residue class modulo 3, `X` (5 x 2) and `Y` (2 x 5) with `Xᵀ M X ≡ C` and
  `Y M X ≡ 1 (mod 3)` (a seed).
* `tr2`, `tr3`: transfer matrices `A = c B + λ w̃ᵀ` (`c = 2, 3`) with `Aᵀ g22 A = c² k6`, where
  `g22 = diag(A₂, 2, 1, 1)`, `k6 = diag(6, 1, 1, 1, 1)` and `w̃ = (0, w)`. If the top four rows of
  a representation `X` of a binary by `K₆` are orthogonal to `w` modulo `c`, then `A X / c`
  represents it by `K₂₂`. The 2-transfers come from 2-neighbours of `K₆` isometric to `K₂₂`, the
  3-transfers from the sublattices `{x : w·x ≡ 0 (mod 3)} ≅ ⟨1, 3⟩ ⊥ A₂ ⊥ ⟨6⟩` of `K₆`, embedded
  in `K₂₂`.
* `k3two`, `k3three` (`Kko112HardData.lean`): witnesses for `[[a, b, 0], [b, c, 0], [0, 0, 1]]` in the
  diagonal sublattices `J32 = ⟨1, 1, 3, 3, 3⟩` and `J33 = ⟨1, 1, 1, 2, 6⟩` of `K₃`, for the doubly hard
  classes (`a, c` even and `b` odd at 2; `ac - b² ≡ 1 (mod 3)` at 3).
Entries are lists, row-major.
"""
import itertools, math, sys
from fractions import Fraction as Fr

K22 = [[1,0,0,0,0],[0,1,0,0,0],[0,0,2,0,0],[0,0,0,2,-1],[0,0,0,-1,2]]
K6 = [[1,0,0,0,0],[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,6]]
g22 = [[2,-1,0,0,0],[-1,2,0,0,0],[0,0,2,0,0],[0,0,0,1,0],[0,0,0,0,1]]
k6 = [[6,0,0,0,0],[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]]

def right_inverse(x, y, p):
    """Y (5 x 2) with Xᵀ Y = 1 (mod p), supported on two rows."""
    for r in range(5):
        for s in range(5):
            if r == s:
                continue
            a, b, c, d = x[r], x[s], y[r], y[s]   # A = [[x_r, x_s], [y_r, y_s]]
            det = (a * d - b * c) % p
            if det == 0:
                continue
            inv = pow(det, -1, p)
            # A⁻¹ = inv * [[d, -b], [-c, a]] ; Ŷ = A⁻¹ gives rows r, s of Y
            Yh = [[(inv * d) % p, (-inv * b) % p], [(-inv * c) % p, (inv * a) % p]]
            Y = [[0, 0] for _ in range(5)]
            Y[r] = Yh[0]
            Y[s] = Yh[1]
            # check
            for i, col in enumerate((x, y)):
                for j in range(2):
                    v = sum(col[k] * Y[k][j] for k in range(5)) % p
                    assert v == (1 if i == j else 0)
            return Y
    raise ValueError('dependent columns')

def mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]

def tr(A): return [list(r) for r in zip(*A)]

def inv(A):
    m = len(A); M = [[Fr(x) for x in r] + [Fr(int(i == j)) for j in range(m)] for i, r in enumerate(A)]
    for i in range(m):
        p = next(r for r in range(i, m) if M[r][i] != 0); M[i], M[p] = M[p], M[i]
        pv = M[i][i]; M[i] = [x / pv for x in M[i]]
        for r in range(m):
            if r != i:
                c = M[r][i]; M[r] = [x - c * y for x, y in zip(M[r], M[i])]
    return [r[m:] for r in M]

def det_int(A):
    m = len(A); M = [[Fr(x) for x in r] for r in A]; d = Fr(1)
    for i in range(m):
        p = next((r for r in range(i, m) if M[r][i] != 0), None)
        if p is None: return 0
        if p != i: M[i], M[p] = M[p], M[i]; d = -d
        d *= M[i][i]
        for r in range(i + 1, m):
            c = M[r][i] / M[i][i]
            M[r] = [x - c * y for x, y in zip(M[r], M[i])]
    return d

def find_isometry(G, H):
    """Integer U with U^T G U = H (both n x n pos def), by backtracking over short vectors."""
    m = len(G)
    Gi = inv(G)
    def Q(v): return sum(v[i] * G[i][j] * v[j] for i in range(m) for j in range(m))
    def B(u, v): return sum(u[i] * G[i][j] * v[j] for i in range(m) for j in range(m))
    maxn = max(H[i][i] for i in range(m))
    bnd = [int(math.isqrt(int(maxn * Gi[i][i])) + 1) for i in range(m)]
    cands = {}
    for v in itertools.product(*[range(-b, b + 1) for b in bnd]):
        q = Q(v)
        if q <= maxn: cands.setdefault(q, []).append(v)
    def rec(cols):
        k = len(cols)
        if k == m:
            U = tr([list(c) for c in cols])
            d = round(float(det_int(U)))
            if abs(d) == 1: return U
            return None
        for v in cands.get(H[k][k], []):
            if all(B(cols[i], v) == H[i][k] for i in range(k)):
                r = rec(cols + [v])
                if r: return r
        return None
    return rec([])

def hnf_basis(gens):
    """Z-basis (rows) of the lattice spanned by rational row vectors gens (common denominator)."""
    den = 1
    for g in gens:
        for x in g: den = den * Fr(x).denominator // math.gcd(den, Fr(x).denominator)
    A = [[int(Fr(x) * den) for x in g] for g in gens]
    m = len(A); row = 0
    for col in range(n):
        while True:
            nz = [r for r in range(row, m) if A[r][col] != 0]
            if not nz: break
            piv = min(nz, key=lambda r: abs(A[r][col]))
            A[row], A[piv] = A[piv], A[row]
            done = True
            for r in range(row + 1, m):
                if A[r][col]:
                    q = A[r][col] // A[row][col]
                    A[r] = [x - q * y for x, y in zip(A[r], A[row])]
                    if A[r][col]: done = False
            if done: break
        if row < m and A[row][col] != 0:
            row += 1
    return [[Fr(x, den) for x in A[r]] for r in range(n)]

def neighbor(v, c):
    """K6^v + Z v/c  (v integral, B(v,v) = 0 mod c^2), basis rows in K6 coordinates."""
    gens = []
    for i in range(n):
        e = [int(i == j) for j in range(n)]
        gens.append([c * x for x in e])
    # kernel of x -> B(x, v) mod c: generated by c*e_i and vectors with B = 0 mod c
    Bv = [sum(K6[i][j] * v[j] for j in range(n)) for i in range(n)]
    for x in itertools.product(range(c), repeat=n):
        if sum(x[i] * Bv[i] for i in range(n)) % c == 0: gens.append(list(x))
    gens.append([Fr(t, c) for t in v])
    return hnf_basis(gens)

def gram_rows(Bs, G):
    return [[sum(b1[i] * G[i][j] * b2[j] for i in range(n) for j in range(n)) for b2 in Bs] for b1 in Bs]

def find_embedding(G, H, detabs):
    """Integer E (5x5) with E^T G E = H and |det E| = detabs."""
    m = len(G)
    Gi = inv(G)
    def Q(v): return sum(v[i] * G[i][j] * v[j] for i in range(m) for j in range(m))
    def B(u, v): return sum(u[i] * G[i][j] * v[j] for i in range(m) for j in range(m))
    maxn = max(H[i][i] for i in range(m))
    bnd = [int(math.isqrt(int(maxn * Gi[i][i])) + 1) for i in range(m)]
    cands = {}
    for v in itertools.product(*[range(-b, b + 1) for b in bnd]):
        q = Q(v)
        if q <= maxn: cands.setdefault(q, []).append(v)
    def rec(cols):
        k = len(cols)
        if k == m:
            U = tr([list(c) for c in cols])
            return U if abs(det_int(U)) == detabs else None
        for v in cands.get(H[k][k], []):
            if all(B(cols[i], v) == H[i][k] for i in range(k)):
                r = rec(cols + [v])
                if r: return r
        return None
    return rec([])

def lll_basis(Bcols, G):
    """LLL-reduce the columns of Bcols w.r.t. G; returns new column matrix."""
    B = tr(Bcols)  # rows
    m = len(B)
    def ip(u, v): return sum(u[i] * G[i][j] * v[j] for i in range(len(u)) for j in range(len(v)))
    def gso():
        mu = [[Fr(0)] * m for _ in range(m)]; nb = [Fr(0)] * m; Bs = []
        for i in range(m):
            v = [Fr(x) for x in B[i]]
            for j in range(i):
                mu[i][j] = sum(Fr(B[i][a]) * G[a][b] * Bs[j][b] for a in range(n) for b in range(n)) / nb[j]
                v = [x - mu[i][j] * y for x, y in zip(v, Bs[j])]
            Bs.append(v); nb[i] = sum(v[a] * G[a][b] * v[b] for a in range(n) for b in range(n))
        return mu, nb
    k = 1; mu, nb = gso()
    while k < m:
        for j in range(k - 1, -1, -1):
            q = round(mu[k][j])
            if q: B[k] = [x - q * y for x, y in zip(B[k], B[j])]; mu, nb = gso()
        if nb[k] >= (Fr(3, 4) - mu[k][k - 1] ** 2) * nb[k - 1]: k += 1
        else: B[k], B[k - 1] = B[k - 1], B[k]; mu, nb = gso(); k = max(k - 1, 1)
    return tr(B)

def mod3_transfers():
    out = {}
    ws = []
    for w in itertools.product(range(3), repeat=4):
        if not any(w) or sum(t * t for t in w) % 3: continue
        # projective representative: first nonzero = 1
        if next(t for t in w if t) != 1: continue
        ws.append(w)
    for w in ws:
        # basis of S_w = {x : w . x_top = 0 mod 3}: columns
        rows = [[3 * int(i == j) for j in range(5)] for i in range(5)]
        for x in itertools.product(range(3), repeat=5):
            if sum(w[i] * x[i] for i in range(4)) % 3 == 0: rows.append(list(x))
        Bs = hnf_basis(rows)
        P = tr([[int(t) for t in r] for r in Bs])
        P = lll_basis(P, K6)
        Gw = mm(mm(tr(P), K6), P)
        E = find_embedding(K22, Gw, 3)
        A = [[3 * x for x in r] for r in mm(E, inv(P))]
        assert all(x.denominator == 1 for r in A for x in r)
        A = [[int(x) for x in r] for r in A]
        assert mm(mm(tr(A), K22), A) == [[9 * x for x in r] for r in K6]
        Dp = [[3 * x for x in r] for r in mm(P, inv(E))]
        assert all(x.denominator == 1 for r in Dp for x in r)
        Dp = [[int(x) for x in r] for r in Dp]
        assert mm(A, Dp) == [[9 * int(i == j) for j in range(5)] for i in range(5)]
        out[w] = (A, Dp)
    return out

def perm(src_to_dst, n=5):
    P = [[0] * n for _ in range(n)]
    for s, d in src_to_dst.items(): P[d][s] = 1
    return P
P22 = perm({0: 3, 1: 4, 2: 2, 3: 0, 4: 1})   # x_g22 = P22 x_K22
P6 = perm({0: 1, 1: 2, 2: 3, 3: 4, 4: 0})    # x_k6 = P6 x_K6
assert mm(mm(tr(P22), g22), P22) == K22
assert mm(mm(tr(P6), k6), P6) == K6
P6i = tr(P6); P22i = tr(P22)

def conv(A, Dp):
    A2 = mm(mm(P22, A), P6i); D2 = mm(mm(P6, Dp), P22i)
    return A2, D2

P22 = perm({0: 3, 1: 4, 2: 2, 3: 0, 4: 1})   # x_g22 = P22 x_K22
P6 = perm({0: 1, 1: 2, 2: 3, 3: 4, 4: 0})    # x_k6 = P6 x_K6
P6i = tr(P6); P22i = tr(P22)

def right_inverse3(cols, p):
    """Y (5 x 3) with Xᵀ Y = 1 (mod p), X = [cols]."""
    for rows in itertools.combinations(range(5), 3):
        A = [[cols[i][r] for r in rows] for i in range(3)]   # 3x3: A[i][k] = X[rows[k]][i]  (Xᵀ restricted)
        # det
        d = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
             + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])) % p
        if d == 0: continue
        di = pow(d, -1, p)
        # inverse of A mod p (adjugate)
        adj = [[0] * 3 for _ in range(3)]
        for i in range(3):
            for j in range(3):
                m = [[A[r][c] for c in range(3) if c != j] for r in range(3) if r != i]
                adj[j][i] = ((-1) ** (i + j)) * (m[0][0] * m[1][1] - m[0][1] * m[1][0])
        Ainv = [[(adj[i][j] * di) % p for j in range(3)] for i in range(3)]
        # Xᵀ Y = A * Yhat where Yhat rows = rows of Y at `rows`; want = I -> Yhat = Ainv
        Y = [[0, 0, 0] for _ in range(5)]
        for k, r in enumerate(rows):
            Y[r] = [Ainv[k][j] for j in range(3)]
        for i in range(3):
            for j in range(3):
                assert sum(cols[i][r] * Y[r][j] for r in range(5)) % p == (1 if i == j else 0)
        return Y
    raise ValueError

def k3table(J, p):
    if p == 2:
        R = 4
        classes = [(a, b, c) for a in range(8) for b in range(4) for c in range(8)]
        hard = lambda a, b, c: a % 2 == 0 and b % 2 == 1 and c % 2 == 0
        md = (8, 4)
    else:
        R = 9
        classes = [(a, b, c) for a in range(9) for b in range(9) for c in range(9)]
        hard = lambda a, b, c: (a * c - b * b) % 3 == 1
        md = (9, 9)
    N = lambda v: sum(J[i] * v[i] * v[i] for i in range(5))
    B = lambda u, v: sum(J[i] * u[i] * v[i] for i in range(5))
    # z = e0 fixed; x, y supported on coords 1..4
    vecs = [v for v in itertools.product(range(R), repeat=5) if v[0] == 0]
    bynorm = {}
    for v in vecs: bynorm.setdefault(N(v) % md[0], []).append(v)
    z = (1, 0, 0, 0, 0)
    out = []
    for (a, b, c) in classes:
        if not hard(a, b, c):
            out.append(([], [])); continue
        wit = None
        for x in bynorm.get(a, []):
            for y in bynorm.get(c, []):
                if B(x, y) % md[1] != b: continue
                try:
                    Y = right_inverse3([x, y, z], p)
                except ValueError:
                    continue
                wit = (x, y, Y); break
            if wit: break
        assert wit, (p, a, b, c)
        x, y, Y = wit
        X = [[x[i], y[i], z[i]] for i in range(5)]
        out.append(([e for r in X for e in r], [e for r in Y for e in r]))
    return out

M22 = [[1,0,0,0,0],[0,1,0,0,0],[0,0,2,0,0],[0,0,0,2,-1],[0,0,0,-1,2]]


M = [[1,0,0,0,0],[0,1,0,0,0],[0,0,2,0,0],[0,0,0,2,-1],[0,0,0,-1,2]]
n = 5
def mv(A, v): return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]

def table2():
    vecs = []
    for v in itertools.product(range(4), repeat=5):
        Mv = mv(M, v)
        g2 = tuple(t % 2 for t in Mv)
        if not any(g2): continue
        vecs.append((v, Mv, g2, sum(v[i] * Mv[i] for i in range(5)) % 8))
    by = {}
    for t in vecs: by.setdefault(t[3], []).append(t)
    out = []
    for a in range(8):
        for b in range(4):
            for c in range(8):
                wit = None
                for (x, Mx, gx, _) in by.get(a, []):
                    for (y, My, gy, _) in by.get(c, []):
                        if gy != gx and sum(x[i] * My[i] for i in range(5)) % 4 == b:
                            wit = (x, y, gx, gy); break
                    if wit: break
                if wit:
                    x, y, gx, gy = wit
                    Y = right_inverse(list(gx), list(gy), 2)    # (Mx)ᵀ Y = 1 mod 2
                    X = [[x[i], y[i]] for i in range(5)]
                    out.append((0, [e for r in X for e in r], [e for r in Y for e in r]))
                else:
                    if a % 4 == 0 and b % 2 == 0: tag = 1
                    elif c % 4 == 0 and b % 2 == 0: tag = 2
                    elif (a + b) % 2 == 0 and (b + c) % 2 == 0 and (a + 2 * b + c) % 4 == 0: tag = 3
                    else: raise ValueError((a, b, c))
                    out.append((tag, [], []))
    return out

def table3():
    vecs = []
    for v in itertools.product(range(3), repeat=5):
        Mv = [t % 3 for t in mv(M, v)]
        if not any(Mv): continue
        vecs.append((v, Mv, sum(v[i] * Mv[i] for i in range(5)) % 3))
    def indep(u, w): return any((u[i] * w[j] - u[j] * w[i]) % 3 for i in range(5) for j in range(i + 1, 5))
    out = []
    for a in range(3):
        for b in range(3):
            for c in range(3):
                wit = None
                for (x, Mx, qa) in vecs:
                    if qa != a: continue
                    for (y, My, qc) in vecs:
                        if qc == c and sum(x[i] * My[i] for i in range(5)) % 3 == b and indep(Mx, My):
                            wit = (x, y, Mx, My); break
                    if wit: break
                assert wit, (a, b, c)
                x, y, Mx, My = wit
                Yr = right_inverse(Mx, My, 3)          # 5 x 2 with (MX)ᵀ Yr = 1, so Y = Yrᵀ: Y M X = 1
                Y = tr(Yr)
                X = [[x[i], y[i]] for i in range(5)]
                out.append(([e for r in X for e in r], [e for r in Y for e in r]))
    return out

def rank_one(A, c, w5):
    """A = c B + lam w5ᵀ (mod c rank one)."""
    j0 = next(j for j in range(5) if w5[j] % c)
    inv_w = pow(w5[j0], -1, c)
    lam = [(A[k][j0] * inv_w) % c for k in range(5)]
    B = [[0] * 5 for _ in range(5)]
    for k in range(5):
        for j in range(5):
            d = A[k][j] - lam[k] * w5[j]
            assert d % c == 0, (A, c, w5)
            B[k][j] = d // c
    return lam, B

def transfers():
    tr2, tr3 = [], []
    for w in itertools.combinations(range(4), 2):
        v = [0] * 5; v[w[0]] = 1; v[w[1]] = 1; v[4] = 1
        Bs = neighbor(v, 2)
        G = [[int(x) for x in r] for r in gram_rows(Bs, K6)]
        U = find_isometry(G, K22)
        Tm = mm(tr(Bs), U)
        A = [[int(2 * x) for x in r] for r in inv(Tm)]
        Dp = [[int(2 * x) for x in r] for r in Tm]
        A2, _ = conv(A, Dp)
        wv = [1 if i in w else 0 for i in range(4)]
        w5 = [0] + wv
        lam, B = rank_one(A2, 2, w5)
        tr2.append((wv, lam, B))
    out3 = mod3_transfers()
    for w, (A, Dp) in out3.items():
        A3, _ = conv(A, Dp)
        w5 = [0] + list(w)
        lam, B = rank_one(A3, 3, w5)
        tr3.append((list(w), lam, B))
    return tr2, tr3

def L(l): return '[' + ', '.join(str(v) for v in l) + ']'

def main_data():
    print('-- Generated by scripts/genus/gen_kko112.py; do not edit.')
    print('import Mathlib.Data.Int.Init')
    print()
    print('/-!')
    print('# Data for `⟨1, 1, 2⟩ ⊥ A₂` (generated)')
    print()
    print('See `scripts/genus/gen_kko112.py`, `KimKimOh/Genus/Kko112Local.lean` and')
    print('`KimKimOh/Genus/Kko112FromK6.lean`.')
    print('-/')
    print()
    print('namespace KimKimOh.Kko112')
    print()
    t2 = table2()
    print('/-- Binary witnesses at 2 for `hostForm 2 2 (-1) 2`, indexed by `32 a + 8 b + c`. -/')
    print('def w22two : List (ℕ × List ℤ × List ℤ) := [')
    print(',\n'.join(f'  ({t}, {L(x)}, {L(y)})' for t, x, y in t2))
    print(']\n')
    t3 = table3()
    print('/-- Binary seeds at 3 for `hostForm 2 2 (-1) 2`, indexed by `9 a + 3 b + c`. -/')
    print('def w22three : List (List ℤ × List ℤ) := [')
    print(',\n'.join(f'  ({L(x)}, {L(y)})' for x, y in t3))
    print(']\n')
    tr2, tr3 = transfers()
    print('/-- The 2-transfers `(w, λ, B)`. -/')
    print('def tr2 : List (List ℤ × List ℤ × List ℤ) := [')
    print(',\n'.join(f'  ({L(w)}, {L(l)}, {L([e for r in B for e in r])})' for w, l, B in tr2))
    print(']\n')
    print('/-- The 3-transfers `(w, λ, B)`. -/')
    print('def tr3 : List (List ℤ × List ℤ × List ℤ) := [')
    print(',\n'.join(f'  ({L(w)}, {L(l)}, {L([e for r in B for e in r])})' for w, l, B in tr3))
    print(']\n')
    print('end KimKimOh.Kko112')


def main_hard():
    t2 = k3table([1, 1, 3, 3, 3], 2)
    t3 = k3table([1, 1, 1, 2, 6], 3)
    print('-- Generated by scripts/genus/gen_kko112.py; do not edit.')
    print('import Mathlib.Data.Int.Init')
    print()
    print('/-!')
    print('# Data for the doubly hard binaries of `⟨1, 1, 2⟩ ⊥ A₂` (generated)')
    print()
    print('See `scripts/genus/gen_kko112.py` and `KimKimOh/Genus/Kko112Hard.lean`.')
    print('-/')
    print()
    print('namespace KimKimOh.Kko112')
    print()
    print('/-- Witnesses `X`, `Y` (5 x 3) for `[[a, b, 0], [b, c, 0], [0, 0, 1]]` in `J32 = ⟨1, 1, 3, 3, 3⟩`,')
    print('indexed by `32 a + 8 b + c`; empty unless `a, c` are even and `b` is odd. -/')
    print('def k3two : List (List ℤ × List ℤ) := [')
    print(',\n'.join(f'  ({L(x)}, {L(y)})' for x, y in t2))
    print(']')
    print()
    print('/-- Witnesses `X`, `Y` (5 x 3) for `[[a, b, 0], [b, c, 0], [0, 0, 1]]` in `J33 = ⟨1, 1, 1, 2, 6⟩`,')
    print('indexed by `81 a + 9 b + c`; empty unless `ac - b² ≡ 1 (mod 3)`. -/')
    print('def k3three : List (List ℤ × List ℤ) := [')
    print(',\n'.join(f'  ({L(x)}, {L(y)})' for x, y in t3))
    print(']')
    print()
    print('end KimKimOh.Kko112')

if __name__ == '__main__':
    main_hard() if sys.argv[1:] == ['hard'] else main_data()

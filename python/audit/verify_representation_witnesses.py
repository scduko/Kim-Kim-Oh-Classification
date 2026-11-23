"""Certificate 4.3(c), Lemmas 2.1–2.2: check the local representations of every terminal matrix."""

import argparse
import gzip
import json
import sys
from collections import Counter
from itertools import combinations, zip_longest
from math import gcd
from pathlib import Path

from certificate_files import GRAM_MATRICES, REPRESENTATION_WITNESSES

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from verification.notation import TARGET_HOSTS

PAIRS = tuple(combinations(range(3), 2))
HOST_DIAGONALS = {
    (6, 2): (1, 1, 3, 3, 3),
    (6, 3): (1, 1, 1, 2, 6),
    (9, 2): (1, 3, 3, 3, 3),
    (9, 3): (1, 1, 2, 3, 6),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def determinant(rows):
    (a, b, c), (d, e, f), (g, h, i) = rows
    return a * (e*i - f*h) - b * (d*i - f*g) + c * (d*h - e*g)


def checked_vector(v, size):
    require(isinstance(v, list) and len(v) == size and all(type(x) is int for x in v),
            "malformed integer vector")
    return v


def enlarged_gram(gram, z, p):
    """Replace the basis vector at the first nonzero entry of z by z/p."""
    if z is None:
        return gram
    checked_vector(z, 3)
    require(all(0 <= t < p for t in z) and any(z), "invalid enlargement generator")
    pivot = next(i for i, t in enumerate(z) if t)
    require(z[pivot] == 1, "enlargement generator is not normalized")
    # The new basis matrix is N/p. It spans an index-p overlattice since
    # p*(z/p)=z and z[pivot]=1 express the omitted basis vector integrally.
    N = [[p * int(i == j) for j in range(3)] for i in range(3)]
    for i in range(3):
        N[i][pivot] = z[i]
    require(determinant(N) == p*p, "incorrect basis-change determinant")
    numerator = [[sum(N[h][i] * gram[h][k] * N[k][j]
                      for h in range(3) for k in range(3))
                  for j in range(3)] for i in range(3)]
    require(all(n % (p*p) == 0 for row in numerator for n in row), "nonintegral overlattice")
    return [[n // (p*p) for n in row] for row in numerator]


def check_local(target, p, gram, proof):
    z, rows = proof
    local = enlarged_gram(gram, z, p)
    require(len(rows) == 5, "local matrix must have five rows")
    for row in rows:
        checked_vector(row, 3)
    require(any(determinant(triple) % p for triple in combinations(rows, 3)),
            "local matrix has column rank less than three")
    # The five recorded rows form X. Check that X^T diag X agrees with
    # the Gram matrix to the moduli of Lemma 2.2. Full column rank modulo
    # p, checked above, makes this a primitive local representation.
    diag = HOST_DIAGONALS[target, p]
    for i in range(3):
        for j in range(i, 3):
            actual = sum(d * row[i] * row[j] for d, row in zip(diag, rows))
            modulus = 9 if p == 3 else (8 if i == j else 4)
            require((actual - local[i][j]) % modulus == 0, "local Gram mismatch")
    return z is not None


def primes_at_least_five(n):
    require(n > 0, "a positive minor gcd was expected")
    for p in (2, 3):
        while n % p == 0:
            n //= p
    p = 5
    while p*p <= n:
        if n % p == 0:
            yield p
            while n % p == 0:
                n //= p
        p += 2
    if n > 1:
        yield n


def check_record(source, record):
    key, v, at_two, at_three = record
    checked_vector(key, 7)
    require(tuple(key) == source, "record does not match the enumerated source")
    target, a, b, c, d, e, f = source
    require(target in (6, 9), "unknown target")
    checked_vector(v, 3)
    require(max(map(abs, v)) <= 2, "covector outside the prescribed box")
    j, scale = TARGET_HOSTS[target]
    G = ((a, b, d), (b, c, e), (d, e, f))
    C = [[G[i][k] - scale * v[i] * v[k] for k in range(3)] for i in range(3)]
    require(C[0][0] > 0 and C[0][0]*C[1][1] > C[0][1]**2 and determinant(C) > 0,
            "correction is not positive definite")
    # Outside the prime divisors of this gcd, C has rank at least two
    # modulo p. At the remaining p >= 5, a diagonal entry in the square
    # class of j supplies the scalar representation in Lemma 2.1.
    minor_gcd = gcd(*(C[r][i] * C[s][k] - C[r][k] * C[s][i]
                      for r, s in PAIRS for i, k in PAIRS))
    for p in primes_at_least_five(minor_gcd):
        require(any(pow(C[i][i] * j, (p-1)//2, p) == 1 for i in range(3)),
                f"missing square class at {p}")
    return (max(map(abs, v)), check_local(target, 2, C, at_two),
            check_local(target, 3, C, at_three))


def check(sources_path, witnesses_path):
    counts = {6: Counter(), 9: Counter()}
    previous = None
    with gzip.open(sources_path, 'rt', encoding='ascii') as sources, \
         gzip.open(witnesses_path, 'rt', encoding='ascii') as records:
        for index, (source_line, witness_line) in enumerate(zip_longest(sources, records), 1):
            require(source_line is not None and witness_line is not None,
                    f"certificate lengths differ at row {index}")
            source = tuple(map(int, source_line.split()))
            require(previous is None or previous < source, f"source order or duplication at row {index}")
            try:
                radius, two, three = check_record(source, json.loads(witness_line))
            except (IndexError, TypeError, KeyError, ValueError) as error:
                raise ValueError(f"row {index}, source {source}: {error}") from error
            counts[source[0]].update(["total", radius, (two, three)])
            previous = source
    for target, count in counts.items():
        expected = 10905 if target == 6 else 7556
        require(count["total"] == expected, f"unexpected terminal census for L{target}")
        norms = tuple(count[r] for r in (0, 1, 2))
        enlargements = tuple(count[k] for k in ((False, False), (True, False),
                                                  (False, True), (True, True)))
        print(f"L{target}: {expected} witnesses; sup norms 0/1/2 {norms}; "
              f"enlargements neither/2 only/3 only/both {enlargements}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources', type=Path, default=GRAM_MATRICES)
    parser.add_argument('--witnesses', type=Path, default=REPRESENTATION_WITNESSES)
    args = parser.parse_args()
    check(args.sources, args.witnesses)

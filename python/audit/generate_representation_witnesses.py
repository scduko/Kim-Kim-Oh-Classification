"""Build the explicit terminal witnesses, using the main verifier for discovery."""

import argparse
import gzip
import json
import sys
from collections import defaultdict
from functools import cache
from itertools import product
from pathlib import Path

from certificate_files import GRAM_MATRICES, REPRESENTATION_WITNESSES, refresh_lean_input

HERE = Path(__file__).resolve().parent
ENTRIES = ((0, 0), (0, 1), (1, 1), (0, 2), (1, 2), (2, 2))


@cache
def weighted_rows(d, p):
    """One actual row for each pair (row direction, Gram contribution)."""
    period = 4 if p == 2 else (3 if d % 3 == 0 else 9)
    moduli = (8, 4, 8, 4, 4, 8) if p == 2 else (9,) * 6
    rows = {}
    for row in product(range(period), repeat=3):
        direction = min(tuple(t % p for t in row), tuple(-t % p for t in row))
        gram = tuple(d * row[i] * row[j] % m for (i, j), m in zip(ENTRIES, moduli))
        rows.setdefault((direction, gram), row)
    return tuple((v, gram, row) for (v, gram), row in rows.items())


def set_bit_indices(bits):
    """Visit set bits in increasing order, in bounded-size integer chunks."""
    data = bits.to_bytes((bits.bit_length() + 7)//8, 'little')
    for start in range(0, len(data), 32):
        word = int.from_bytes(data[start:start+32], 'little')
        while word:
            bit = word & -word
            yield 8*start + bit.bit_length() - 1
            word -= bit


def local_matrices(target, p, needed, local):
    """Backtrack explicit row choices through the finite Gram enumeration."""
    space = local.residues(p)
    moduli = space.moduli
    full = frozenset(product(range(p), repeat=3))
    zero = frozenset(((0, 0, 0),))
    # Each layer maps row span to the bit set of its achievable Gram residues.
    layers = [{zero: 1}]
    from notation import TARGET_HOSTS
    host, _ = TARGET_HOSTS[target]
    diagonals = local.HOST_DIAGONALS[host, p]
    for depth, d in enumerate(diagonals, 1):
        following = {}
        for span, codes in layers[-1].items():
            for direction, gram, row in weighted_rows(d, p):
                enlarged = local.extend(span, direction, p)
                if len(enlarged) * p**(5-depth) < p**3:
                    continue
                translated = local.translated(codes, moduli, gram)
                following[enlarged] = following.get(enlarged, 0) | translated
        layers.append(following)

    pending = {full: set(needed)}
    predecessors = []
    for layer in range(5, 0, -1):
        d = diagonals[layer-1]
        unresolved = {}
        for span, keys in pending.items():
            as_bytes = bytearray((space.size+7)//8)
            for key in keys:
                as_bytes[key//8] |= 1 << (key % 8)
            unresolved[span] = int.from_bytes(as_bytes, 'little')
        previous = defaultdict(set)
        links = {}
        for span, codes in layers[layer-1].items():
            for direction, gram, row in weighted_rows(d, p):
                enlarged = local.extend(span, direction, p)
                waiting = unresolved.get(enlarged, 0)
                if not waiting:
                    continue
                reached = waiting & local.translated(codes, moduli, gram)
                if not reached:
                    continue
                unresolved[enlarged] ^= reached
                for key in set_bit_indices(reached):
                    original = space.encode(*((n-g) % m for n, g, m in
                                              zip(space.decode(key), gram, moduli)))
                    previous[span].add(original)
                    links[enlarged, key] = ((span, original), row)
            if not any(unresolved.values()):
                break
        if any(unresolved.values()):
            raise ArithmeticError(f"could not reconstruct Gram residues for L{target} at {p}")
        predecessors.append(links)
        pending = previous
    matrices = {}
    for code in needed:
        state = (full, code)
        rows = []
        for links in predecessors:
            state, row = links[state]
            rows.append(row)
        if state != (zero, 0):
            raise ArithmeticError("incomplete backward walk")
        matrices[code] = rows[::-1]
    return matrices


def local_choice(host, p, gram, local):
    """Identify a direct residue or record the generator for an index-p enlargement."""
    space = local.residues(p)
    def encode(g):
        return space.encode(*(n % m for n, m in zip(g, space.moduli)))
    if local.represents(host, p, gram):
        return None, encode(gram)
    from terminal_corrections import enlargements
    for line, larger_gram in enlargements(gram, p):
        if local.represents(host, p, larger_gram):
            return line, encode(larger_gram)
    raise ArithmeticError("local evidence is missing")


def generate(sources_path, witnesses_path, verification):
    sys.path.insert(0, str(verification.resolve()))
    import local_representation as local
    from notation import TARGET_HOSTS
    from terminal_corrections import find

    records = []
    needed = defaultdict(set)
    with gzip.open(sources_path, 'rt', encoding='ascii') as source:
        for line in source:
            key = tuple(map(int, line.split()))
            target, *gram = key
            host, scale = TARGET_HOSTS[target]
            covector = find(target, tuple(gram))
            if covector is None:
                raise ArithmeticError(f"missing covector for {key}")
            corrected = tuple(n-scale*covector[i]*covector[j] for n, (i, j) in zip(gram, ENTRIES))
            choices = []
            for p in (2, 3):
                generator, code = local_choice(host, p, corrected, local)
                needed[target, p].add(code)
                choices.append((generator, code))
            records.append((key, covector, choices))
    matrices = {}
    for (target, p), codes in sorted(needed.items()):
        print(f"Reconstructing {len(codes)} different local Gram residues for L{target} at {p}",
              flush=True)
        matrices[target, p] = local_matrices(target, p, codes, local)
    with witnesses_path.open('wb') as stream, \
         gzip.GzipFile(filename='', fileobj=stream, mode='wb', mtime=0) as out:
        for key, covector, choices in records:
            proof = [[z, matrices[key[0], p][code]] for p, (z, code) in zip((2, 3), choices)]
            out.write((json.dumps([key, covector, *proof], separators=(',', ':'))+'\n').encode('ascii'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources', type=Path, default=GRAM_MATRICES)
    parser.add_argument('--witnesses', type=Path, default=REPRESENTATION_WITNESSES)
    parser.add_argument('--verification', type=Path, default=HERE.parent/'verification')
    args = parser.parse_args()
    generate(args.sources, args.witnesses, args.verification)
    refresh_lean_input(args.witnesses)

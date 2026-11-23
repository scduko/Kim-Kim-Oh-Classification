"""Certificates 4.1–4.2 (§4.1 and A.2). Rebuild the profiles with --verify-tables and check the determinant ranges."""
import argparse
import csv
import json
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import accumulate, product
from math import isqrt, prod
from operator import mul
from pathlib import Path


from certificate_files import LOCAL_STEPS

HERE = Path(__file__).resolve().parent
FIELDS = ("host_determinant", "prime", "first_entry", "multiplicity", "steps_by_x")
sys.path.insert(0, str(HERE.parent))
from verification.notation import (FIRST_ENTRIES, MAX_SX_SQUARED, PERIODIC_START, SCALES,
                                   SIGNED_DIVISOR_WIDTH, TAIL_COEFFICIENT)
SIGNED_DIVISORS = (-6, -3, -2, -1, 1, 2, 3, 6)
PRIMES = [n for n in range(5, 128) if all(n % d for d in range(2, isqrt(n) + 1))]
PRODUCTS = [1, *accumulate(PRIMES, mul)]


def shift_axis(table, radix, stride, shift):
    """Move each byte forward by shift in one digit of a mixed-radix index."""
    if not shift:
        return table
    block = radix * stride
    distance = shift * stride
    result = bytearray(len(table))
    if block < len(table) // block:
        for position in range(block):
            result[(position + distance) % block::block] = table[position::block]
    else:
        for start in range(0, len(table), block):
            split = start + block - distance
            result[start:start + distance] = table[split:start + block]
            result[start + distance:start + block] = table[start:split]
    return result


def allowed_directions(accepted, prime, scale, moduli):
    """Intersect translated acceptance tables for *all* lifts of each direction."""
    period = 9 if prime == 3 else (4 if scale == 1 else 2)
    masks = {}
    for v in product(range(period), repeat=3):
        x, y, k = v
        products = (x*x, x*y, y*y, x*k, y*k, k*k)
        translated = accepted
        stride = len(accepted)
        for entry, radix in zip(products, moduli):
            stride //= radix
            translated = shift_axis(translated, radix, stride, scale * entry % radix)
        direction = tuple(n % prime for n in v)
        bits = int.from_bytes(translated, "little")
        masks[direction] = masks.get(direction, bits) & bits
    return [masks[v].to_bytes(len(accepted), "little")
            for v in product(range(prime), repeat=3)]


@cache
def profile(prime, flags):
    """Return the possible pairs of arithmetic progression steps for each x.

    Each row fixes y and lists the permitted k modulo p. A step of 1
    allows all residues and a step of p fixes one. The residue for k may
    depend on y. Omit a pair if another pair has smaller or equal steps
    in both coordinates.
    """
    options = []
    for x in range(prime):
        rows = [flags[(x*prime + y)*prime:(x*prime + y + 1)*prime]
                for y in range(prime)]
        steps = []
        if all(all(row) for row in rows):
            steps.append((1, 1))
        else:
            if all(any(row) for row in rows):
                steps.append((1, prime))
            if any(all(row) for row in rows):
                steps.append((prime, 1))
            if not steps and any(any(row) for row in rows):
                steps.append((prime, prime))
        options.append(tuple(steps))
    return tuple(options)


def rebuild(directory, compare_directions=False):
    sys.path.insert(0, str(directory))
    from local_representation import acceptance_table, source_flags
    from residue_census import permissible

    records = Counter()
    for host, scale in SCALES.items():
        for prime in (2, 3):
            moduli = (8, 4, 8, 4, 4, 8) if prime == 2 else (9,) * 6
            accepted = acceptance_table(host, prime)
            expected = {(3,2): 28420, (9,2): 22624, (3,3): 451386, (9,3): 355485}
            if sum(accepted) != expected[host, prime]:
                raise ValueError(("Table 3 representation count", host, prime))
            stride = prod(moduli[1:])
            directions = allowed_directions(accepted, prime, scale, moduli)
            if compare_directions:
                lookup = permissible(host, prime)
                for z, flags in zip(product(range(prime), repeat=3), directions):
                    if flags != lookup[z]:
                        raise ValueError(f"all-lifts test disagrees for K{host}, p={prime}, z={z}")
            for i, row in enumerate(zip(source_flags(prime), *directions)):
                if row[0]:
                    records[host, prime, i // stride, profile(prime, row[1:])] += 1
    return records


def write_records(path, records):
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(FIELDS)
        for (host, prime, a, options), n in sorted(records.items()):
            writer.writerow([host, prime, a, n, json.dumps(options, separators=(",", ":"))])


def read_records(path):
    records = Counter()
    with path.open(encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if tuple(reader.fieldnames or ()) != FIELDS:
            raise ValueError("unexpected profile table header")
        for row in reader:
            host, prime, a, count = (int(row[key]) for key in FIELDS[:4])
            options = tuple(tuple(tuple(pair) for pair in steps)
                            for steps in json.loads(row["steps_by_x"]))
            key = host, prime, a, options
            if (host not in SCALES or prime not in (2, 3) or count <= 0
                    or not 0 <= a < (8 if prime == 2 else 9)
                    or len(options) != prime or key in records
                    or any(pair not in tuple(product((1, prime), repeat=2))
                           for steps in options for pair in steps)):
                raise ValueError(f"invalid profile on line {reader.line_num}")
            records[key] = count
    return records


@cache
def signed_divisor_works(host, a, step):
    if a > MAX_SX_SQUARED:
        return False
    primes = [p for p in PRIMES if a % p == 0]
    allowed = {p: {host * r*r % p for r in range(p)} for p in primes}
    scale = SCALES[host]
    for c in range(prod(primes)):
        possible_starts = {y % step for y in SIGNED_DIVISORS
                           if all(c % p == 0 or (c-scale*y*y) % p in allowed[p] for p in primes)}
        if len(possible_starts) < step:
            return False
    return True


def group_records(records):
    groups = defaultdict(set)
    for host in SCALES:
        for prime, expected in [(2, 21504), (3, 459108)]:
            if sum(n for (j, p, a, opts), n in records.items()
                   if (j, p) == (host, prime)) != expected:
                raise ValueError(f"wrong maximal-source population for K{host} at {prime}")
    for host, prime, a, options in records:
        groups[host, prime, a % (4 if prime == 2 else 3)].add(options)
    return groups


def uniform_gap_bounds():
    if sum(Fraction(1, p) for p in PRIMES[:26]) >= 1:
        raise ArithmeticError("small-t bound")
    gap_bounds = []
    for t in range(27):
        g = 1
        while True:
            excluded = sum((g + p - 1) // p for p in PRIMES[:t])
            if g > excluded:
                break
            # The union bound is nondecreasing, so every skipped g fails too.
            g = excluded + 1
        gap_bounds.append(g)
    g27 = 31 * 2**25
    if (3 * PRODUCTS[27] <= 4 * (TAIL_COEFFICIENT * g27**2)**2 or
            PRIMES[27] * 31**4 <= 16 * 32**4):
        raise ArithmeticError("large-t bound")
    return gap_bounds


def uniform_ranges(host, groups, gap_bounds):
    """Independently calculate inclusive (a,t,low,high) for all remaining blocks."""
    scale = SCALES[host]

    @cache
    def triples(a_class):
        cases = set()
        for left, right in product(groups[host, 2, a_class % 4], groups[host, 3, a_class % 3]):
            choices = frozenset((x, h2*h3, m2*m3)
                                for x in FIRST_ENTRIES
                                for h2, m2 in left[x % 2] for h3, m3 in right[x % 3])
            cases.add(choices)
        if not cases:
            raise ValueError(f"missing local cases for K{host}, a={a_class} mod 12")
        return cases

    @cache
    def retained(a):
        cases = set()
        for choices in triples(a % 12):
            valid = frozenset((x,h,m) for x,h,m in choices
                              if scale*x*x < a and (x or signed_divisor_works(host,a,h)))
            if not valid:
                raise ValueError(f"uncovered local case for K{host}, a={a}, {choices}")
            cases.add(valid)
        return cases

    @cache
    def bound(a, t):
        g = gap_bounds[t]
        @cache
        def scalar_cost(option):
            x,h,m = option
            w = h*g if x else SIGNED_DIVISOR_WIDTH
            return Fraction(scale * a, a - scale*x*x) * (
                Fraction(w*w, 4) + Fraction((m*g)**2, 3))
        # The source fixes the pair of local profiles. Minimize over the
        # choices for that pair before taking the worst bound over sources.
        return max(min(map(scalar_cost, options)) for options in retained(a))

    for t in range(27):
        candidates = list(range(2, PERIODIC_START))
        for first in range(PERIODIC_START, PERIODIC_START + 12):
            beta_bound = bound(first, t)
            if 3*PRODUCTS[t] <= 4*beta_bound*beta_bound:
                candidates.extend(range(first, int(4*beta_bound/3)+1, 12))
        for a in sorted(candidates):
            low = max(PRODUCTS[t], (3*a*a+3)//4)
            high = min(PRODUCTS[t+1]-1, int(a * bound(a, t)))
            if low <= high:
                yield a, t, low, high


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--verify-tables", action="store_true")
    mode.add_argument("--export", action="store_true", help="regenerate local_progression_steps.tsv")
    parser.add_argument("--verification-dir", type=Path, default=HERE.parent / "verification")
    args = parser.parse_args()
    path = LOCAL_STEPS
    if args.export:
        write_records(path, rebuild(args.verification_dir))
    records = read_records(path)
    if args.verify_tables and rebuild(args.verification_dir, compare_directions=True) != records:
        raise ValueError("recorded profiles differ from the full-precision table scan")
    groups = group_records(records)
    gap_bounds = uniform_gap_bounds()
    for host, expected in [(3, (494, Fraction(86153, 200))), (9, (855, Fraction(42642, 59)))]:
        sizes = [tuple(len(groups[host, p, r]) for r in range(4 if p == 2 else 3))
                 for p in (2, 3)]
        ranges = list(uniform_ranges(host, groups, gap_bounds))
        if len(ranges) != {3: 536, 9: 1136}[host]:
            raise ValueError(("Certificate 4.2 range count", host, len(ranges)))
        if args.verify_tables:
            from scalar_sieve import ranges as search_ranges
            search_intervals = sorted(
                (a, t, lo, hi)
                for a, intervals in search_ranges(host).items() for t, lo, hi in intervals)
            if sorted(ranges) != search_intervals:
                raise ValueError(f"binary search intervals disagree for K{host}")
        actual = max(a for a, _, _, _ in ranges), max(Fraction(hi,a) for a, _, _, hi in ranges)
        if actual != expected:
            raise ValueError(f"cutoffs disagree for K{host}: {actual}")
        print(f"K{host}: profiles at 2 {sizes[0]}, at 3 {sizes[1]}; "
              f"{len(ranges)} nonempty (a,t) ranges; a <= {actual[0]}, beta <= {actual[1]}.")
    print("Local choices (x,h,m) verified.")


if __name__ == "__main__":
    main()

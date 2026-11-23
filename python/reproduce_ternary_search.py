"""Reproduce the local tables, determinant ranges, and finite search for the ternary universality of L6 and L9."""
import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent / "verification"))
import bounded_exact
import scalar_sieve
import local_representation


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=1,
                        help="number of processes for the bounded enumeration")
    parser.add_argument("--all-blocks", action="store_true",
                        help="apply the last-column test to all blocks in the uniform ranges of §4.1")
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    local_representation.main()
    scalar_sieve.main()
    bounded_exact.verify(args.workers, args.all_blocks)
    print("All checks passed.")


if __name__ == "__main__":
    main()

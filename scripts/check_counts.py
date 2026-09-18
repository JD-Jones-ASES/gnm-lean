#!/usr/bin/env python3
"""Cross-check the classification of the number of good partitions with the standard library.

A good partition of {1, ..., n} is a set of pairwise disjoint nonempty blocks of at most three
integers covering {1, ..., n}, each block summing to a power of three. This script recomputes, in
plain Python with exact integers and no dependence on the Lean development:

  * the exact number of good partitions at the twenty values whose exact count the classification
    consumes, and compares it with the classification's prediction;
  * that at least three good partitions exist at every n at most eighty outside the two
    exceptional sets;
  * that a permutation of the centred interval with one hole, whose displacements run through the
    nonzero values of that interval, exists at every hole for every radius from four to eight;
  * two controls whose failure is the expected outcome.

Python 3.9 or later, standard library only. Run from anywhere:

    python scripts/check_counts.py
"""

import sys

POWERS = [3 ** k for k in range(9)]
POWER_SET = set(POWERS)

# The twenty values whose exact count the classification consumes.
EXACT_VALUES = list(range(1, 15)) + [21, 23, 30, 32, 75, 86]

failures = []


def report(ok, line):
    """Print one check and remember a failure."""
    print(("ok    " if ok else "FAIL  ") + line)
    if not ok:
        failures.append(line)


def is_nu(n):
    """n lies in the set on which the good partition is unique."""
    if n in (1, 2, 3, 4):
        return True
    for t in range(2, 12):
        p = 3 ** t
        if n + 4 == p or n + 2 == p or n + 1 == p or n == p:
            return True
        if n in (p + 1, p + 2, p + 3, p + 5):
            return True
        if p > 3 * (n + 6):
            break
    return False


def is_e2(n):
    """n lies in the set on which there are exactly two good partitions."""
    if n == 13:
        return True
    for t in range(2, 12):
        p = 3 ** t
        if n + 3 == p:
            return True
        if t >= 3 and n + 6 == p:
            return True
        if p > 3 * (n + 6):
            break
    return False


def predicted(n):
    """The classification's prediction at n: 1, 2, or 3 meaning "at least three"."""
    if is_nu(n):
        return 1
    if is_e2(n):
        return 2
    return 3


def blocks_at(x, present):
    """Every good block whose largest element is x and whose other elements are still uncovered."""
    out = []
    if x in POWER_SET:
        out.append((x,))
    for total in POWERS:
        rest = total - x
        if rest < 1:
            continue
        if rest > 2 * x:
            break
        if rest < x and present[rest]:
            out.append((x, rest))
        # A triple x > a > b >= 1 with x + a + b = total: a determines b = rest - a, and
        # rest / 2 < a < min(x, rest).
        for a in range(rest // 2 + 1, min(x, rest)):
            b = rest - a
            if b >= 1 and present[a] and present[b]:
                out.append((x, a, b))
    return out


def count_partitions(n, limit=None):
    """The number of good partitions of {1, ..., n}, stopping early once limit is reached."""
    present = [False] + [True] * n

    def walk(high):
        while high >= 1 and not present[high]:
            high -= 1
        if high == 0:
            return 1
        found = 0
        for block in blocks_at(high, present):
            for y in block:
                present[y] = False
            found += walk(high - 1)
            for y in block:
                present[y] = True
            if limit is not None and found >= limit:
                break
        return found

    return walk(n)


def displacement_permutation(k, j):
    """A permutation of [-k, k] minus {j} whose displacements are the nonzero values of [-k, k].

    Returns the permutation as a dict, or None when the search is exhausted.
    """
    domain = [u for u in range(-k, k + 1) if u != j]
    shifts = [d for d in range(-k, k + 1) if d != 0]
    order = sorted(domain, key=lambda u: abs(u), reverse=True)
    taken_shift = set()
    taken_image = set()
    chosen = {}

    def walk(index):
        if index == len(order):
            return True
        u = order[index]
        for d in shifts:
            if d in taken_shift:
                continue
            image = u + d
            if image < -k or image > k or image == j or image in taken_image:
                continue
            taken_shift.add(d)
            taken_image.add(image)
            chosen[u] = image
            if walk(index + 1):
                return True
            taken_shift.discard(d)
            taken_image.discard(image)
            del chosen[u]
        return False

    return dict(chosen) if walk(0) else None


def shifted_permutation(k, j, omitted):
    """As above, but with the displacement set omitting `omitted` instead of zero."""
    domain = [u for u in range(-k, k + 1) if u != j]
    shifts = [d for d in range(-k, k + 1) if d != omitted]
    taken_shift = set()
    taken_image = set()

    def walk(index):
        if index == len(domain):
            return True
        u = domain[index]
        for d in shifts:
            if d in taken_shift:
                continue
            image = u + d
            if image < -k or image > k or image == j or image in taken_image:
                continue
            taken_shift.add(d)
            taken_image.add(image)
            if walk(index + 1):
                return True
            taken_shift.discard(d)
            taken_image.discard(image)
        return False

    return walk(0)


def good_partition_check(n, blocks):
    """True when `blocks` is a good partition of {1, ..., n}."""
    seen = []
    for block in blocks:
        if not block or len(block) > 3 or len(set(block)) != len(block):
            return False
        if sum(block) not in POWER_SET:
            return False
        seen.extend(block)
    return sorted(seen) == list(range(1, n + 1))


def main():
    print("Good partitions of {1, ..., n}: blocks of at most three integers, sums powers of three.")
    print("")
    print("Exact counts at the twenty values the classification consumes:")
    for n in EXACT_VALUES:
        want = predicted(n)
        got = count_partitions(n)
        plural = "partition" if got == 1 else "partitions"
        if want == 3:
            report(got >= 3, f"n = {n}: {got} good {plural}, at least three predicted")
        else:
            report(got == want,
                   f"n = {n}: {got} good {plural}, {want} predicted"
                   + (" (unique)" if want == 1 else " (exactly two)"))

    print("")
    print("At least three good partitions at every n at most eighty outside the exceptional sets:")
    sweep = [n for n in range(1, 81) if predicted(n) == 3]
    short = [n for n in sweep if count_partitions(n, limit=3) < 3]
    report(not short,
           f"{len(sweep)} values from {min(sweep)} to {max(sweep)}: three good partitions found "
           "at each" + ("" if not short else f"; short at {short}"))

    print("")
    print("Permutations of the centred interval with one hole and all nonzero displacements:")
    for k in range(4, 9):
        missing = [j for j in range(-k, k + 1) if displacement_permutation(k, j) is None]
        report(not missing,
               f"radius {k}: a permutation at each of the {2 * k + 1} holes"
               + ("" if not missing else f"; none at {missing}"))

    print("")
    print("Controls:")
    wrong = [[6, 2], [5, 4], [3, 1]]
    report(not good_partition_check(6, wrong),
           "control: the blocks {6, 2}, {5, 4}, {3, 1} of sums 8, 9, 4 are not a good partition "
           "of {1, ..., 6}, as they must not be")
    report(not shifted_permutation(4, 0, 1),
           "control: at radius 4 no permutation has displacements omitting 1 instead of 0, as "
           "there must not be")

    print("")
    if failures:
        print(f"{len(failures)} CHECK(S) FAILED")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

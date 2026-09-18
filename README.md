# The number of partitions of {1, …, n} into sets of at most three elements with power-of-three sums

Call a finite set of integers a *good block* when it is nonempty, has at most three elements and
sums to a power of three (the exponent may be zero, so `{1}` is one). A *good partition* of
`{1, …, n}` is a set of pairwise disjoint good blocks whose union is `{1, …, n}`, and `count n` is
the number of them.

Gurvich and Naumova, *Partitioning set [n] = {1, …, n} into subsets of size at most m such that all
sums are powers of m*, [arXiv:2508.00946v3](https://arxiv.org/abs/2508.00946v3) (v3, July 2026),
conjecture that a good partition exists for every `n`, prove in their Theorem 3 that it is unique
for every `n` in the set `N_u` below, record that there are exactly two at `n = 3^t − 3` and at
`n = 13`, and conjecture, immediately after that theorem, that the number is greater than two at
every other `n`, reporting a computer check of the conjecture up to `n = 844`. The family
`n = 3^t − 6` with `t ≥ 3` also has exactly two — its first member `21` lies inside that reported
range, and the count there is fixed by an exhaustive search checked by Lean's kernel — so the
conjecture as printed does not hold. The four theorems here give the complete classification; the
converse of the source's uniqueness statement is proved here as well. Write

- `N_u = {1, 2, 3, 4} ∪ {3^t − 4, 3^t − 2, 3^t − 1, 3^t, 3^t + 1, 3^t + 2, 3^t + 3, 3^t + 5 : t ≥ 2}`,
- `E_2 = {13} ∪ {3^t − 3 : t ≥ 2} ∪ {3^t − 6 : t ≥ 3}`.

The four theorems (the first and third for `n ≥ 1`; `count 0 = 1` by the empty partition):

- `count n = 1` if and only if `n ∈ N_u` — `GNM.count_eq_one_iff`;
- `count n = 2` if and only if `n ∈ E_2` — `GNM.count_eq_two_iff`;
- `count n ≥ 3` if and only if `n` lies in neither set — `GNM.three_le_count_iff`;
- `count (3^t − 6) = 2` for every `t ≥ 3` — `GNM.count_eq_two_of_add_six`.

The lower bounds are three explicit good partitions, built by strong induction on `n` from a finite
base of tabulated partitions at `n ≤ 80` through four transports, each of which keeps a component
that can be read back off the result: a partition of a smaller interval with a frame of triples
around a power of three, in a symmetric and in a signed form; the canonical pairs `{d, Q − d}` below
a power; and a lift from one power to a larger one. Three distinct frames come from an explicit
symmetric family, its negation and one of three trades, and from gluing a Langford pairing to an arbitrary prefix
permutation, where three prefixes give three permutations and so three frames. The exact values `1`
and `2` are exhaustive enumerations at twenty values `n ≤ 86`, checked by the kernel and complete by
a theorem about the search, carried to every power of three by stabilization: above a threshold every
pair with a large deficit is forced to be canonical, so truncation inverts the lift and `count` is
constant along each family.

The directory `GN/` is an unchanged copy of the `gn-lean` development at commit
`73bb87b16da8c053fd07e0d4dc43732b74335a3b` (registered as PALOMAR-2026-09-07-000013; MIT; the same
author), which proves that every `{1, …, n}` has a good partition; this repository uses its objects
and theorems and adds the counting layer in `GNM/`.

Nothing is claimed at any base other than three, so the source's question for general `m` is
untouched; no asymptotics and no closed form for `count n` are proved.

As of 2026-09-17 no treatment of this multiplicity classification was located in a bounded search of
arXiv, OEIS, MathOverflow and the Palomar registry; the count of additive permutations in Donovan
and Grannell (2018) concerns the total over all holes and is not used here.

Run locally with the pinned Lean and Mathlib versions; there are no GitHub Actions workflows.

```sh
lake build
python scripts/check-source.py
python scripts/check_counts.py
```

[PROOF.md](PROOF.md) gives the mathematics with the Lean name of every step,
[VERIFICATION.md](VERIFICATION.md) the checks and their limits, and [DISCLOSURE.md](DISCLOSURE.md)
the assistance statement. [Challenge.lean](Challenge.lean) states the four theorems;
[Solution.lean](Solution.lean) proves them.

License: [MIT](LICENSE).

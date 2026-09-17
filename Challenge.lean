import Mathlib

/-!
# The number of partitions of {1, …, n} into sets of at most three elements with power-of-three sums

Call a finite set of integers a good block when it is nonempty, has at most three elements and its
sum is `3 ^ k` for some natural number `k` (so `3 ^ 0 = 1` is allowed). A good partition of
`{1, …, n}` is a finite set of pairwise disjoint good blocks whose union is exactly `{1, …, n}`,
and `count n` is the number of good partitions of `{1, …, n}`. Gurvich and Naumova
(arXiv:2508.00946v3) conjectured that every `{1, …, n}` has a good partition, proved that the
partition is unique exactly on the set `N_u` below (their Theorem 3), listed the values with exactly
two partitions as `{13} ∪ {3^t − 3 : t ≥ 2}`, and conjectured that every other `n` has more than two.

The theorems below give the complete classification: `count n = 1` exactly on `N_u`; `count n = 2`
exactly on `E_2 = {13} ∪ {3^t − 3 : t ≥ 2} ∪ {3^t − 6 : t ≥ 3}`; and `count n ≥ 3` for every other
`n ≥ 1`. The last theorem states the family `n = 3^t − 6` (`t ≥ 3`) on its own: each of its members
has exactly two good partitions, so the conjecture as printed does not hold there.

The interval is written with bounds rather than as an interval constant. The value `n = 0` has the
empty partition and nothing else, so `count 0 = 1`; it lies outside the classification, which is why
two theorems assume `1 ≤ n`.

This Mathlib-only file intentionally contains placeholders. The corresponding Solution declarations
are proved in a separate environment.
-/

namespace GNM

/-- `blocks` is a good partition of `{1, …, n}`: the blocks cover exactly the integers `x` with
`1 ≤ x ≤ n`, they are pairwise disjoint, and each block is nonempty, has at most three elements and
sums to `3 ^ k` for some natural number `k`. -/
def IsGoodPartition (n : ℕ) (blocks : Finset (Finset ℤ)) : Prop :=
  (∀ x : ℤ, (∃ b ∈ blocks, x ∈ b) ↔ (1 ≤ x ∧ x ≤ (n : ℤ))) ∧
  (∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c) ∧
  ∀ b ∈ blocks, b.Nonempty ∧ b.card ≤ 3 ∧ ∃ k : ℕ, b.sum id = (3 : ℤ) ^ k

/-- The number of good partitions of `{1, …, n}`. -/
noncomputable def count (n : ℕ) : ℕ :=
  Nat.card {blocks : Finset (Finset ℤ) // IsGoodPartition n blocks}

/-- Membership in `N_u = {1, 2, 3, 4} ∪ {3^t − 4, 3^t − 2, 3^t − 1, 3^t, 3^t + 1, 3^t + 2, 3^t + 3,
3^t + 5 : t ≥ 2}`, the set on which the good partition is unique. -/
def Nu (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    ∃ t : ℕ, 2 ≤ t ∧ (n + 4 = 3 ^ t ∨ n + 2 = 3 ^ t ∨ n + 1 = 3 ^ t ∨ n = 3 ^ t ∨
      n = 3 ^ t + 1 ∨ n = 3 ^ t + 2 ∨ n = 3 ^ t + 3 ∨ n = 3 ^ t + 5)

/-- Membership in `E_2 = {13} ∪ {3^t − 3 : t ≥ 2} ∪ {3^t − 6 : t ≥ 3}`, the set on which there are
exactly two good partitions. -/
def E2 (n : ℕ) : Prop :=
  n = 13 ∨ (∃ t : ℕ, 2 ≤ t ∧ n + 3 = 3 ^ t) ∨ (∃ t : ℕ, 3 ≤ t ∧ n + 6 = 3 ^ t)

/-- `{1, …, n}` has exactly one good partition if and only if `n ∈ N_u`. -/
theorem count_eq_one_iff (n : ℕ) (hn : 1 ≤ n) : count n = 1 ↔ Nu n := by
  sorry

/-- `{1, …, n}` has exactly two good partitions if and only if `n ∈ E_2`. -/
theorem count_eq_two_iff (n : ℕ) : count n = 2 ↔ E2 n := by
  sorry

/-- `{1, …, n}` has at least three good partitions if and only if `n` lies in neither `N_u` nor
`E_2`. -/
theorem three_le_count_iff (n : ℕ) (hn : 1 ≤ n) : 3 ≤ count n ↔ ¬ Nu n ∧ ¬ E2 n := by
  sorry

/-- For every `t ≥ 3`, `{1, …, 3^t − 6}` has exactly two good partitions. -/
theorem count_eq_two_of_add_six (n t : ℕ) (ht : 3 ≤ t) (h : n + 6 = 3 ^ t) : count n = 2 := by
  sorry

end GNM

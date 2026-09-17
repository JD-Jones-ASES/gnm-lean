import Mathlib

/-!
# The compared definitions

The four definitions of `Challenge.lean`, repeated character for character so that the development
can use them without importing the challenge environment.
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

end GNM

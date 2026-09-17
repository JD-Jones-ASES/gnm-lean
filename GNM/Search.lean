import GNM.Witness

/-!
# The exhaustive search and its completeness

The good partitions of a small interval are enumerated by a depth-first search that repeatedly takes
the largest uncovered element and tries every good block containing it. The search is a Boolean
function the kernel evaluates: it returns true when every partition it reaches is one of a
prescribed list. Its completeness theorem turns that Boolean verdict into the statement that the
prescribed list is all of the good partitions, which is what the exact counts at small values rest
on. The recursion is driven by a supply of steps, one for each element still to be covered, so no
well-founded recursion enters a term the kernel must reduce.
-/

namespace GNM

open GN

/-- Candidate completeness: a good block of the interval that contains the largest remaining element
is one of the generated candidates. -/
theorem mem_candidates_of {x : ℕ} {rest : List ℕ} (hsorted : rest.Pairwise (· > ·))
    (hlt : ∀ a ∈ rest, a < x) {B : Finset ℤ} (hx : (x : ℤ) ∈ B) (hsub : B ⊆ toBlock (x :: rest))
    (hcard : B.card ≤ 3) (hsum : ∃ k : ℕ, B.sum id = (3 : ℤ) ^ k) :
    ∃ b ∈ candidates x rest, toBlock b = B := by
  sorry

/-- The search invariant: if the search from `rest` with the blocks of `acc` already chosen accepts,
then every good partition of the set of `rest`, together with those blocks, is one of the expected
partitions. -/
theorem searchAll_complete (expected : List (List (List ℕ))) (fuel : ℕ) (rest : List ℕ)
    (acc : List (List ℕ)) (hsorted : rest.Pairwise (· > ·)) (hfuel : rest.length ≤ fuel)
    (h : searchAll expected fuel rest acc = true) :
    ∀ bs : Finset (Finset ℤ), GoodOn (toBlock rest) bs →
      ∃ w ∈ expected, toBlocks acc ∪ bs = toBlocks w := by
  sorry

/-- An accepting search lists every good partition of `{1, …, n}`. -/
theorem complete_of_search {n : ℕ} {expected : List (List (List ℕ))}
    (h : search n expected = true) :
    ∀ bs, IsGoodPartition n bs → ∃ w ∈ expected, bs = toBlocks w := by
  sorry

/-- One checked witness and an accepting search against it give a count of one. -/
theorem count_eq_one_of_search {n : ℕ} {w : List (List ℕ)} (hw : checkPartition n w = true)
    (h : search n [w] = true) : count n = 1 := by
  sorry

/-- Two checked, differing witnesses and an accepting search against them give a count of two. -/
theorem count_eq_two_of_search {n : ℕ} {w₁ w₂ : List (List ℕ)} (h₁ : checkPartition n w₁ = true)
    (h₂ : checkPartition n w₂ = true) (hd : differ w₁ w₂ = true)
    (h : search n [w₁, w₂] = true) : count n = 2 := by
  sorry

end GNM

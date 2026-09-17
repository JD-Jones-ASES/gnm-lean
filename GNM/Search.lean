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

/-- The two-element blocks with largest entry `x` and second entry from the list. -/
def pairsWith (x : ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | a :: t => if isPow3 (x + a) then [x, a] :: pairsWith x t else pairsWith x t

/-- The three-element blocks with entries `x`, `a` and a smaller third entry from the list. -/
def triplesFrom (x a : ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | b :: t =>
      if Nat.blt b a && isPow3 (x + a + b) then [x, a, b] :: triplesFrom x a t
      else triplesFrom x a t

/-- The three-element blocks with largest entry `x` and two further entries from the list. -/
def triplesWith (x : ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | a :: t => triplesFrom x a t ++ triplesWith x t

/-- Every good block with largest entry `x` and further entries from `rest`, each block written in
decreasing order. -/
def candidates (x : ℕ) (rest : List ℕ) : List (List ℕ) :=
  (if isPow3 x then [[x]] else []) ++ (pairsWith x rest ++ triplesWith x rest)

/-- The list with the entries of `b` removed, the order kept. -/
def removeAll (rest : List ℕ) (b : List ℕ) : List ℕ := rest.filter (fun x => !memB x b)

/-- The search: true when every good partition of `rest`, together with the blocks already chosen in
`acc`, occurs in `expected`. The first argument is the supply of steps. -/
def searchAll : ℕ → List ℕ → List (List ℕ) → List (List (List ℕ)) → Bool
  | _, [], acc, expected => expected.contains acc.reverse
  | 0, _ :: _, _, _ => false
  | fuel + 1, x :: rest, acc, expected =>
      allB (fun B => searchAll fuel (removeAll rest B) (B :: acc) expected) (candidates x rest)

/-- The list `[n, n − 1, …, 1]`. -/
def descending : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n + 1) :: descending n

/-- The search over `{1, …, n}`. -/
def search (n : ℕ) (expected : List (List (List ℕ))) : Bool :=
  searchAll n (descending n) [] expected

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
theorem searchAll_complete (fuel : ℕ) (rest : List ℕ) (acc : List (List ℕ))
    (expected : List (List (List ℕ))) (hsorted : rest.Pairwise (· > ·)) (hfuel : rest.length ≤ fuel)
    (h : searchAll fuel rest acc expected = true) :
    ∀ bs : Finset (Finset ℤ), GoodOn (toBlock rest) bs →
      ∃ w ∈ expected, toBlocks acc ∪ bs = toBlocks w := by
  sorry

/-- An accepting search lists every good partition of `{1, …, n}`. -/
theorem complete_of_search {n : ℕ} {expected : List (List (List ℕ))}
    (h : search n expected = true) :
    ∀ bs, IsGoodPartition n bs → ∃ w ∈ expected, bs = toBlocks w := by
  sorry

/-- One checked witness and an accepting search against it give a count of one. -/
theorem count_eq_one_of_search {n : ℕ} {w : List (List ℕ)} (hw : partitionOK n w = true)
    (h : search n [w] = true) : count n = 1 := by
  sorry

/-- Two checked, differing witnesses and an accepting search against them give a count of two. -/
theorem count_eq_two_of_search {n : ℕ} {w₁ w₂ : List (List ℕ)} (h₁ : partitionOK n w₁ = true)
    (h₂ : partitionOK n w₂ = true) (hd : differ w₁ w₂ = true) (h : search n [w₁, w₂] = true) :
    count n = 2 := by
  sorry

end GNM

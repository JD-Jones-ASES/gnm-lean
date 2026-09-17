import GNM.Basic
import GNM.SearchDefs

/-!
# Checkers on lists, and their bridges to the partition predicate

Explicit partitions and explicit zero-sum frames are carried as lists of lists of numbers, and their
defining properties are decided by the Boolean functions of `GNM.SearchDefs`, which the kernel
evaluates directly. Each checker is paired with a bridge theorem saying that a list passing it names
a good partition, respectively a partition into zero-sum triples, of the intended set, and that two
lists whose blocks differ name different partitions.
-/

namespace GNM

open GN

/-- The set of integers named by a list of numbers. -/
def toBlock (b : List ℕ) : Finset ℤ := (b.map (fun x => (x : ℤ))).toFinset

/-- The set of blocks named by a list of lists of numbers. -/
def toBlocks (bs : List (List ℕ)) : Finset (Finset ℤ) := (bs.map toBlock).toFinset

/-- The power-of-three test is correct on the range it covers. -/
theorem isPow3_iff {n : ℕ} (hn : n < 2187) : isPow3 n = true ↔ ∃ k : ℕ, n = 3 ^ k := by
  sorry

/-- The occurrence test is correct. -/
theorem memList_iff {y : ℕ} {l : List ℕ} : memList y l = true ↔ y ∈ l := by
  sorry

/-- The repetition test is correct. -/
theorem noDup_iff {l : List ℕ} : noDup l = true ↔ l.Nodup := by
  sorry

/-- The sum of a list. -/
theorem sumList_eq (l : List ℕ) : sumList l = l.sum := by
  sorry

/-- The length of a list. -/
theorem lenList_eq (l : List ℕ) : lenList l = l.length := by
  sorry

/-- The entries of a list of blocks. -/
theorem flat_eq (bs : List (List ℕ)) : flat bs = bs.flatten := by
  sorry

/-- The range test is correct. -/
theorem inRange_iff {n : ℕ} {l : List ℕ} : inRange n l = true ↔ ∀ y ∈ l, 1 ≤ y ∧ y ≤ n := by
  sorry

/-- The universal test over a list of blocks is correct. -/
theorem allB_iff {f : List ℕ → Bool} {l : List (List ℕ)} :
    allB f l = true ↔ ∀ b ∈ l, f b = true := by
  sorry

/-- The block test is correct: a good block is a nonempty list of at most three entries whose sum is
a power of three. -/
theorem goodBlock_iff {b : List ℕ} :
    goodBlock b = true ↔ b ≠ [] ∧ b.length ≤ 3 ∧ ∃ k : ℕ, b.sum = 3 ^ k := by
  sorry

/-- A list that passes the partition checker names a good partition of `{1, …, n}`. -/
theorem isGoodPartition_of_checkPartition {n : ℕ} {bs : List (List ℕ)}
    (h : checkPartition n bs = true) : IsGoodPartition n (toBlocks bs) := by
  sorry

/-- Two checked lists with a block of the first matching no block of the second name different
partitions. -/
theorem toBlocks_ne_of_differ {n : ℕ} {bs cs : List (List ℕ)} (hb : checkPartition n bs = true)
    (hc : checkPartition n cs = true) (h : differ bs cs = true) : toBlocks bs ≠ toBlocks cs := by
  sorry

/-- Three checked, pairwise differing lists give a count of at least three. -/
theorem three_le_count_of_witnesses {n : ℕ} {w₁ w₂ w₃ : List (List ℕ)}
    (h₁ : checkPartition n w₁ = true) (h₂ : checkPartition n w₂ = true)
    (h₃ : checkPartition n w₃ = true) (d₁₂ : differ w₁ w₂ = true) (d₁₃ : differ w₁ w₃ = true)
    (d₂₃ : differ w₂ w₃ = true) : 3 ≤ count n := by
  sorry

/-- The set of integers named by a list of integers. -/
def toBlockZ (b : List ℤ) : Finset ℤ := b.toFinset

/-- The set of triples named by a list of lists of integers. -/
def toBlocksZ (bs : List (List ℤ)) : Finset (Finset ℤ) := (bs.map toBlockZ).toFinset

/-- A list that passes the frame checker names a partition of the support into zero-sum triples. -/
theorem zeroPartition_of_framesOK {s : Finset ℤ} {support : List ℤ} (hs : support.toFinset = s)
    (hnd : noDupZ support = true) {bs : List (List ℤ)} (h : framesOK support bs = true) :
    ZeroPartition s (toBlocksZ bs) := by
  sorry

/-- Two checked frames with a triple of the first matching no triple of the second are different. -/
theorem toBlocksZ_ne_of_differZ {support : List ℤ} {bs cs : List (List ℤ)}
    (hb : framesOK support bs = true) (hc : framesOK support cs = true)
    (h : differZ bs cs = true) : toBlocksZ bs ≠ toBlocksZ cs := by
  sorry

end GNM

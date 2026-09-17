import GNM.Basic

/-!
# Checkers on lists, and their bridges to the partition predicate

Explicit partitions and explicit zero-sum frames are carried as lists of lists of numbers, and their
defining properties are decided by the Boolean functions below, all of them plain structural
recursions that the kernel evaluates directly. Each checker is paired with a bridge theorem saying
that a list passing it names a good partition, respectively a partition into zero-sum triples, of
the intended set, and that two lists whose blocks differ name different partitions.
-/

namespace GNM

open GN

/-- Auxiliary for the power-of-three test: divide by three while possible, with the supply of
divisions bounded by the first argument. -/
def isPow3Aux : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, n =>
      if Nat.beq n 1 then true
      else if Nat.beq (n % 3) 0 && Nat.ble 3 n then isPow3Aux fuel (n / 3) else false

/-- `isPow3 n` is true exactly when `n` is a power of three. -/
def isPow3 (n : ℕ) : Bool := isPow3Aux n n

/-- Occurrence of a number in a list. -/
def memB (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: t => Nat.beq x y || memB x t

/-- A list of numbers with no repetition. -/
def nodupB : List ℕ → Bool
  | [] => true
  | x :: t => !memB x t && nodupB t

/-- The sum of a list of numbers. -/
def sumB : List ℕ → ℕ
  | [] => 0
  | x :: t => x + sumB t

/-- A good block as a list: nonempty, at most three elements, no repetition, power-of-three sum. -/
def blockOK (b : List ℕ) : Bool :=
  !b.isEmpty && Nat.ble b.length 3 && nodupB b && isPow3 (sumB b)

/-- The set of integers named by a list of numbers. -/
def toBlock (b : List ℕ) : Finset ℤ := (b.map (fun x => (x : ℤ))).toFinset

/-- The set of blocks named by a list of lists of numbers. -/
def toBlocks (bs : List (List ℕ)) : Finset (Finset ℤ) := (bs.map toBlock).toFinset

/-- All the entries of a list of blocks, in order. -/
def flat : List (List ℕ) → List ℕ
  | [] => []
  | b :: bs => b ++ flat bs

/-- A Boolean test holds of every block of a list. -/
def allB (f : List ℕ → Bool) : List (List ℕ) → Bool
  | [] => true
  | b :: bs => f b && allB f bs

/-- Every entry of a list lies in `[1, n]`. -/
def inRangeB (n : ℕ) : List ℕ → Bool
  | [] => true
  | x :: t => Nat.ble 1 x && Nat.ble x n && inRangeB n t

/-- A good partition of `{1, …, n}` as a list: good blocks, no entry repeated, `n` entries in all,
every entry in `[1, n]`. -/
def partitionOK (n : ℕ) (bs : List (List ℕ)) : Bool :=
  allB blockOK bs && nodupB (flat bs) && Nat.beq (flat bs).length n && inRangeB n (flat bs)

/-- Every entry of the first list occurs in the second. -/
def allMemB : List ℕ → List ℕ → Bool
  | [], _ => true
  | x :: t, c => memB x c && allMemB t c

/-- Two blocks with no repetitions name the same set: same length, and every entry of the first in
the second. -/
def sameBlock (b c : List ℕ) : Bool := Nat.beq b.length c.length && allMemB b c

/-- Some block of the list names the same set as `b`. -/
def matchesSome (b : List ℕ) : List (List ℕ) → Bool
  | [] => false
  | c :: cs => sameBlock b c || matchesSome b cs

/-- Some block of the first list matches no block of the second. -/
def differ : List (List ℕ) → List (List ℕ) → Bool
  | [], _ => false
  | b :: bs, cs => !matchesSome b cs || differ bs cs

/-- The power-of-three test is correct. -/
theorem isPow3_iff (n : ℕ) : isPow3 n = true ↔ ∃ k : ℕ, n = 3 ^ k := by
  sorry

/-- The occurrence test is correct. -/
theorem memB_iff {x : ℕ} {l : List ℕ} : memB x l = true ↔ x ∈ l := by
  sorry

/-- The repetition test is correct. -/
theorem nodupB_iff {l : List ℕ} : nodupB l = true ↔ l.Nodup := by
  sorry

/-- A list that passes the partition checker names a good partition of `{1, …, n}`. -/
theorem isGoodPartition_of_partitionOK {n : ℕ} {bs : List (List ℕ)}
    (h : partitionOK n bs = true) : IsGoodPartition n (toBlocks bs) := by
  sorry

/-- Two checked lists with a block of the first matching no block of the second name different
partitions. -/
theorem toBlocks_ne_of_differ {n : ℕ} {bs cs : List (List ℕ)} (hb : partitionOK n bs = true)
    (hc : partitionOK n cs = true) (h : differ bs cs = true) : toBlocks bs ≠ toBlocks cs := by
  sorry

/-- Three checked, pairwise differing lists give a count of at least three. -/
theorem three_le_count_of_witnesses {n : ℕ} {w₁ w₂ w₃ : List (List ℕ)}
    (h₁ : partitionOK n w₁ = true) (h₂ : partitionOK n w₂ = true) (h₃ : partitionOK n w₃ = true)
    (d₁₂ : differ w₁ w₂ = true) (d₁₃ : differ w₁ w₃ = true) (d₂₃ : differ w₂ w₃ = true) :
    3 ≤ count n := by
  sorry

/-- Occurrence of an integer in a list. -/
def memZ (x : ℤ) : List ℤ → Bool
  | [] => false
  | y :: t => (x == y) || memZ x t

/-- A list of integers with no repetition. -/
def nodupZ : List ℤ → Bool
  | [] => true
  | x :: t => !memZ x t && nodupZ t

/-- The sum of a list of integers. -/
def sumZ : List ℤ → ℤ
  | [] => 0
  | x :: t => x + sumZ t

/-- A zero-sum triple as a list: three entries, no repetition, sum zero. -/
def zeroTripleOK (b : List ℤ) : Bool := Nat.beq b.length 3 && nodupZ b && decide (sumZ b = 0)

/-- The set of integers named by a list of integers. -/
def toBlockZ (b : List ℤ) : Finset ℤ := b.toFinset

/-- The set of triples named by a list of lists of integers. -/
def toBlocksZ (bs : List (List ℤ)) : Finset (Finset ℤ) := (bs.map toBlockZ).toFinset

/-- All the entries of a list of triples, in order. -/
def flatZ : List (List ℤ) → List ℤ
  | [] => []
  | b :: bs => b ++ flatZ bs

/-- A Boolean test holds of every triple of a list. -/
def allZ (f : List ℤ → Bool) : List (List ℤ) → Bool
  | [] => true
  | b :: bs => f b && allZ f bs

/-- Every entry of the first list of integers occurs in the second. -/
def allMemZ : List ℤ → List ℤ → Bool
  | [], _ => true
  | x :: t, c => memZ x c && allMemZ t c

/-- A frame checker: every triple zero-sum, no entry repeated, and the entries are exactly the
prescribed support. -/
def framesOK (support : List ℤ) (bs : List (List ℤ)) : Bool :=
  allZ zeroTripleOK bs && nodupZ (flatZ bs) &&
    Nat.beq (flatZ bs).length support.length && allMemZ support (flatZ bs)

/-- Two triples with no repetitions name the same set. -/
def sameBlockZ (b c : List ℤ) : Bool := Nat.beq b.length c.length && allMemZ b c

/-- Some triple of the list names the same set as `b`. -/
def matchesSomeZ (b : List ℤ) : List (List ℤ) → Bool
  | [] => false
  | c :: cs => sameBlockZ b c || matchesSomeZ b cs

/-- Some triple of the first list matches no triple of the second. -/
def differZ : List (List ℤ) → List (List ℤ) → Bool
  | [], _ => false
  | b :: bs, cs => !matchesSomeZ b cs || differZ bs cs

/-- A list that passes the frame checker names a partition of the support into zero-sum triples. -/
theorem zeroPartition_of_framesOK {s : Finset ℤ} {support : List ℤ} (hs : support.toFinset = s)
    (hnd : nodupZ support = true) {bs : List (List ℤ)} (h : framesOK support bs = true) :
    ZeroPartition s (toBlocksZ bs) := by
  sorry

/-- Two checked frames with a triple of the first matching no triple of the second are different. -/
theorem toBlocksZ_ne_of_differZ {support : List ℤ} {bs cs : List (List ℤ)}
    (hb : framesOK support bs = true) (hc : framesOK support cs = true)
    (h : differZ bs cs = true) : toBlocksZ bs ≠ toBlocksZ cs := by
  sorry

end GNM

/-!
# Kernel-evaluated checkers and the exhaustive search

This module imports nothing. Its functions are the ones Lean's kernel evaluates in the finite
facts of the development: a checker for explicit good partitions of `{1, …, n}`, a checker for
zero-sum triple partitions, and an exhaustive search over the good partitions of `{1, …, n}` that
takes the largest uncovered element first. Every recursion is written with an explicit recursor
and marked `noncomputable`; the completeness of the search and the meaning of the checkers are
theorems of the modules that import this one.

For a block `[x, a, b]` with `1 ≤ b < a`, the sum lies strictly between `x + a` and `x + 2a`, so
with the power of three `3 ^ k` fixed and `s = 3 ^ k − x`, the third element `b = s − a` is
determined; the search generates the blocks containing `x` from the at most two powers of three
that can occur at `x` and tests one membership per `a`.
-/

namespace GNM

/-- The powers of three below `3 ^ 7`; every block sum considered here is below `3 ^ 7`. -/
def pow3s : List Nat := [1, 3, 9, 27, 81, 243, 729]

/-- `y` occurs in `l`. -/
noncomputable def memList (y : Nat) (l : List Nat) : Bool :=
  List.rec false (fun z _ ih => Nat.beq y z || ih) l

/-- `isPow3 n` is `true` exactly when `n = 3 ^ k` for some `k`, for `n < 3 ^ 7`. -/
def isPow3 (n : Nat) : Bool :=
  Nat.beq n 1 || Nat.beq n 3 || Nat.beq n 9 || Nat.beq n 27 || Nat.beq n 81 ||
    Nat.beq n 243 || Nat.beq n 729

/-- The values `a` with `0 < a < x` for which `x + a` is a power of three. -/
noncomputable def pairNeeds (x : Nat) : List Nat :=
  List.rec [] (fun P _ ih => if Nat.blt x P && Nat.blt P (x + x) then (P - x) :: ih else ih) pow3s

/-- The values `s` for which `x + s` is a power of three and `s` can be the sum of two distinct
elements below `x`. -/
noncomputable def tripNeeds (x : Nat) : List Nat :=
  List.rec [] (fun P _ ih => if Nat.ble (x + 3) P && Nat.ble (P - x) (x + x) then (P - x) :: ih
    else ih) pow3s

/-- The elements of `t` that do not occur in `B`, in the order of `t`. -/
noncomputable def removeAll (B : List Nat) (t : List Nat) : List Nat :=
  List.rec [] (fun y _ ih => if memList y B then ih else y :: ih) t

/-- Every good block containing `x` whose other elements come from `rest` (descending, all
below `x`, without repetition), each block listed in descending order. -/
noncomputable def candidates (x : Nat) (rest : List Nat) : List (List Nat) :=
  let pn := pairNeeds x
  let tn := tripNeeds x
  List.rec (if isPow3 x then [[x]] else [])
    (fun a t ih =>
      let ih2 :=
        List.rec ih
          (fun s _ jh =>
            if Nat.blt a s && Nat.blt s (a + a) && memList (s - a) t then [x, a, s - a] :: jh
            else jh)
          tn
      if memList a pn then [x, a] :: ih2 else ih2)
    rest

/-- `f` holds of every member of `l`. -/
noncomputable def allB (f : List Nat → Bool) (l : List (List Nat)) : Bool :=
  List.rec true (fun B _ ih => f B && ih) l

/-- `f` holds of every element of `l`. -/
noncomputable def allNat (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun y _ ih => f y && ih) l

/-- `[n, n − 1, …, 1]`. -/
noncomputable def downFrom (n : Nat) : List Nat :=
  Nat.rec [] (fun m ih => (m + 1) :: ih) n

/-- The exhaustive search: `true` exactly when every good partition of the elements of `rest`,
extended by the blocks of `acc`, is a member of `expected`. The search takes the largest element
first, so it visits every good partition once, in the form "blocks descending inside, listed by
decreasing largest element". -/
noncomputable def searchAll (expected : List (List (List Nat))) :
    Nat → List Nat → List (List Nat) → Bool :=
  fun fuel =>
    Nat.rec (motive := fun _ => List Nat → List (List Nat) → Bool)
      (fun rest acc => List.rec (expected.contains acc.reverse) (fun _ _ _ => false) rest)
      (fun _ ih rest acc =>
        List.rec (expected.contains acc.reverse)
          (fun x t _ => allB (fun B => ih (removeAll B t) (B :: acc)) (candidates x t)) rest)
      fuel

/-- `true` exactly when every good partition of `{1, …, n}` occurs in `expected`. -/
noncomputable def search (n : Nat) (expected : List (List (List Nat))) : Bool :=
  searchAll expected n (downFrom n) []

/-- `l` followed by `r`. -/
noncomputable def appList (l r : List Nat) : List Nat :=
  List.rec r (fun y _ ih => y :: ih) l

/-- The sum of `l`. -/
noncomputable def sumList (l : List Nat) : Nat :=
  List.rec 0 (fun y _ ih => y + ih) l

/-- The length of `l`. -/
noncomputable def lenList (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => ih + 1) l

/-- No repeated element. -/
noncomputable def noDup (l : List Nat) : Bool :=
  List.rec true (fun y t ih => !memList y t && ih) l

/-- All the elements of the blocks of `bs`. -/
noncomputable def flat (bs : List (List Nat)) : List Nat :=
  List.rec [] (fun b _ ih => appList b ih) bs

/-- Every element of `l` lies in `[1, n]`. -/
noncomputable def inRange (n : Nat) (l : List Nat) : Bool :=
  List.rec true (fun y _ ih => Nat.ble 1 y && Nat.ble y n && ih) l

/-- A nonempty list of at most three elements whose sum is a power of three. -/
noncomputable def goodBlock (b : List Nat) : Bool :=
  match b with
  | [] => false
  | _ :: _ => Nat.ble (lenList b) 3 && isPow3 (sumList b)

/-- `bs` is a good partition of `{1, …, n}`: good blocks, no repeated element, `n` elements in
all, every element in `[1, n]`. -/
noncomputable def checkPartition (n : Nat) (bs : List (List Nat)) : Bool :=
  allB goodBlock bs &&
    (let f := flat bs
     noDup f && Nat.beq (lenList f) n && inRange n f)

/-- Two blocks with the same elements: equal lengths and every element of `b` in `c`. -/
noncomputable def sameBlock (b c : List Nat) : Bool :=
  Nat.beq (lenList b) (lenList c) && allNat (fun y => memList y c) b

/-- `bs` has a block that matches no block of `cs`, so the two partitions differ. -/
noncomputable def differ (bs cs : List (List Nat)) : Bool :=
  List.rec false
    (fun b _ ih => !(List.rec false (fun c _ jh => sameBlock b c || jh) cs) || ih) bs

/-! ### Zero-sum triple partitions of a finite set of integers -/

/-- `y` occurs in `l`. -/
noncomputable def memListZ (y : Int) (l : List Int) : Bool :=
  List.rec false (fun z _ ih => (y == z) || ih) l

/-- The length of `l`. -/
noncomputable def lenListZ (l : List Int) : Nat :=
  List.rec 0 (fun _ _ ih => ih + 1) l

/-- The sum of `l`. -/
noncomputable def sumListZ (l : List Int) : Int :=
  List.rec 0 (fun y _ ih => y + ih) l

/-- No repeated element. -/
noncomputable def noDupZ (l : List Int) : Bool :=
  List.rec true (fun y t ih => !memListZ y t && ih) l

/-- All the elements of the blocks of `bs`. -/
noncomputable def flatZ (bs : List (List Int)) : List Int :=
  List.rec [] (fun b _ ih => List.rec ih (fun y _ jh => y :: jh) b) bs

/-- Three distinct integers summing to zero. -/
noncomputable def zeroTripleOK (b : List Int) : Bool :=
  Nat.beq (lenListZ b) 3 && noDupZ b && (sumListZ b == 0)

/-- `bs` partitions the elements of `support` (a list without repetition) into zero-sum triples:
every block is a zero-sum triple, the blocks' elements do not repeat, there are as many of them
as `support` has, and each lies in `support`. -/
noncomputable def framesOK (support : List Int) (bs : List (List Int)) : Bool :=
  List.rec true (fun b _ ih => zeroTripleOK b && ih) bs &&
    (let f := flatZ bs
     noDupZ f && Nat.beq (lenListZ f) (lenListZ support) &&
       List.rec true (fun y _ ih => memListZ y support && ih) f)

/-- Two blocks with the same elements. -/
noncomputable def sameBlockZ (b c : List Int) : Bool :=
  Nat.beq (lenListZ b) (lenListZ c) && List.rec true (fun y _ ih => memListZ y c && ih) b

/-- `bs` has a block that matches no block of `cs`. -/
noncomputable def differZ (bs cs : List (List Int)) : Bool :=
  List.rec false
    (fun b _ ih => !(List.rec false (fun c _ jh => sameBlockZ b c || jh) cs) || ih) bs

end GNM

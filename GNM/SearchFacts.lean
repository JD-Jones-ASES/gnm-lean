import GNM.SearchDefs
import GNM.Data.BaseWitnesses

/-!
# The kernel-checked finite facts

This module imports nothing from Mathlib. Every theorem in it is a closed computation checked by
Lean's kernel: the tabulated partitions pass the checker of `GNM.SearchDefs`, the partitions
tabulated at one value have pairwise different blocks, and at the twenty values whose exact count
the classification consumes the exhaustive search accepts the tabulated list, which says that the
list is all of the good partitions there. The modules that import this one turn these facts into
statements about good partitions of the interval and about their number, and evaluate nothing
themselves.

Each fact names the entries of the table by position, so that one name carries everything the
finite base needs at one value.
-/

namespace GNM

/-- The partition tabulated at `n` in position `i`, and the empty list when the table lists
fewer. -/
def wAt (n i : Nat) : List (List Nat) := (baseWitnesses n).getD i []

/-- A Boolean test holds of every partition in a list of partitions. -/
noncomputable def allW (f : List (List Nat) → Bool) (ws : List (List (List Nat))) : Bool :=
  List.rec true (fun v _ ih => f v && ih) ws

/-- A Boolean test holds at every natural number below a bound. -/
noncomputable def upTo (f : Nat → Bool) : Nat → Bool :=
  Nat.rec true (fun m ih => f m && ih)

/-- Every partition tabulated at `n` passes the checker for `{1, …, n}`. -/
noncomputable def witnessesOK (n : Nat) : Bool :=
  allW (fun v => checkPartition n v) (baseWitnesses n)

/-- Every tabulated partition, at every value at most eighty-six, is a good partition of its own
interval. -/
noncomputable def allWitnessesOK : Bool := upTo witnessesOK 87

/-- The first three partitions tabulated at `n` are good partitions of `{1, …, n}`, and each of
the three pairs has a block on one side that the other side does not have. -/
noncomputable def threeOK (n : Nat) : Bool :=
  checkPartition n (wAt n 0) && checkPartition n (wAt n 1) && checkPartition n (wAt n 2) &&
    differ (wAt n 0) (wAt n 1) && differ (wAt n 0) (wAt n 2) && differ (wAt n 1) (wAt n 2)

/-- The first partition tabulated at `n` is a good partition of `{1, …, n}`. -/
noncomputable def oneOK (n : Nat) : Bool := checkPartition n (wAt n 0)

/-- The first two partitions tabulated at `n` are good partitions of `{1, …, n}`, and the first
has a block the second does not have. -/
noncomputable def twoOK (n : Nat) : Bool :=
  checkPartition n (wAt n 0) && checkPartition n (wAt n 1) && differ (wAt n 0) (wAt n 1)

/-- The left half of a true conjunction is true. -/
theorem and_fst {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => exact h

/-- The right half of a true conjunction is true. -/
theorem and_snd {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => exact Bool.noConfusion h

/-- A test true at every value below a bound is true at each of those values. -/
theorem upTo_apply {f : Nat → Bool} {k : Nat} :
    ∀ N : Nat, upTo f N = true → k < N → f k = true := by
  intro N
  induction N with
  | zero => intro _ hk; omega
  | succ m ih =>
      intro h hk
      cases Nat.lt_or_ge k m with
      | inl hlt => exact ih (and_snd h) hlt
      | inr hge =>
          have hkm : k = m := by omega
          rw [hkm]
          exact and_fst h

/-- The six facts the finite base reads off `threeOK`. -/
theorem threeOK_facts {n : Nat} (h : threeOK n = true) :
    checkPartition n (wAt n 0) = true ∧ checkPartition n (wAt n 1) = true ∧
      checkPartition n (wAt n 2) = true ∧ differ (wAt n 0) (wAt n 1) = true ∧
      differ (wAt n 0) (wAt n 2) = true ∧ differ (wAt n 1) (wAt n 2) = true := by
  have h6 : (checkPartition n (wAt n 0) && checkPartition n (wAt n 1) &&
      checkPartition n (wAt n 2) && differ (wAt n 0) (wAt n 1) &&
      differ (wAt n 0) (wAt n 2) && differ (wAt n 1) (wAt n 2)) = true := h
  exact ⟨and_fst (and_fst (and_fst (and_fst (and_fst h6)))),
    and_snd (and_fst (and_fst (and_fst (and_fst h6)))),
    and_snd (and_fst (and_fst (and_fst h6))), and_snd (and_fst (and_fst h6)),
    and_snd (and_fst h6), and_snd h6⟩

/-- The three facts the finite base reads off `twoOK`. -/
theorem twoOK_facts {n : Nat} (h : twoOK n = true) :
    checkPartition n (wAt n 0) = true ∧ checkPartition n (wAt n 1) = true ∧
      differ (wAt n 0) (wAt n 1) = true := by
  have h3 : (checkPartition n (wAt n 0) && checkPartition n (wAt n 1) &&
      differ (wAt n 0) (wAt n 1)) = true := h
  exact ⟨and_fst (and_fst h3), and_snd (and_fst h3), and_snd h3⟩

/-- Every tabulated partition is a good partition of its own interval. -/
theorem allWitnessesOK_true : allWitnessesOK = true := by decide +kernel

/-- Every partition tabulated at a value at most eighty-six passes the checker there. -/
theorem witnessesOK_true {n : Nat} (hn : n < 87) : witnessesOK n = true :=
  upTo_apply 87 allWitnessesOK_true hn

/-! ### Three good, pairwise different partitions at the values at most eighty outside the
two exceptional sets -/

/-- Three of the tabulated partitions of `{1, …, 15}` are good and pairwise different. -/
theorem three_ok_15 : threeOK 15 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 16}` are good and pairwise different. -/
theorem three_ok_16 : threeOK 16 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 17}` are good and pairwise different. -/
theorem three_ok_17 : threeOK 17 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 18}` are good and pairwise different. -/
theorem three_ok_18 : threeOK 18 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 19}` are good and pairwise different. -/
theorem three_ok_19 : threeOK 19 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 20}` are good and pairwise different. -/
theorem three_ok_20 : threeOK 20 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 22}` are good and pairwise different. -/
theorem three_ok_22 : threeOK 22 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 31}` are good and pairwise different. -/
theorem three_ok_31 : threeOK 31 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 33}` are good and pairwise different. -/
theorem three_ok_33 : threeOK 33 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 34}` are good and pairwise different. -/
theorem three_ok_34 : threeOK 34 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 35}` are good and pairwise different. -/
theorem three_ok_35 : threeOK 35 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 36}` are good and pairwise different. -/
theorem three_ok_36 : threeOK 36 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 37}` are good and pairwise different. -/
theorem three_ok_37 : threeOK 37 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 38}` are good and pairwise different. -/
theorem three_ok_38 : threeOK 38 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 39}` are good and pairwise different. -/
theorem three_ok_39 : threeOK 39 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 40}` are good and pairwise different. -/
theorem three_ok_40 : threeOK 40 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 41}` are good and pairwise different. -/
theorem three_ok_41 : threeOK 41 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 42}` are good and pairwise different. -/
theorem three_ok_42 : threeOK 42 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 43}` are good and pairwise different. -/
theorem three_ok_43 : threeOK 43 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 44}` are good and pairwise different. -/
theorem three_ok_44 : threeOK 44 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 45}` are good and pairwise different. -/
theorem three_ok_45 : threeOK 45 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 46}` are good and pairwise different. -/
theorem three_ok_46 : threeOK 46 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 47}` are good and pairwise different. -/
theorem three_ok_47 : threeOK 47 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 48}` are good and pairwise different. -/
theorem three_ok_48 : threeOK 48 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 49}` are good and pairwise different. -/
theorem three_ok_49 : threeOK 49 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 50}` are good and pairwise different. -/
theorem three_ok_50 : threeOK 50 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 51}` are good and pairwise different. -/
theorem three_ok_51 : threeOK 51 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 52}` are good and pairwise different. -/
theorem three_ok_52 : threeOK 52 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 53}` are good and pairwise different. -/
theorem three_ok_53 : threeOK 53 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 54}` are good and pairwise different. -/
theorem three_ok_54 : threeOK 54 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 55}` are good and pairwise different. -/
theorem three_ok_55 : threeOK 55 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 56}` are good and pairwise different. -/
theorem three_ok_56 : threeOK 56 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 57}` are good and pairwise different. -/
theorem three_ok_57 : threeOK 57 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 58}` are good and pairwise different. -/
theorem three_ok_58 : threeOK 58 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 59}` are good and pairwise different. -/
theorem three_ok_59 : threeOK 59 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 60}` are good and pairwise different. -/
theorem three_ok_60 : threeOK 60 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 61}` are good and pairwise different. -/
theorem three_ok_61 : threeOK 61 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 62}` are good and pairwise different. -/
theorem three_ok_62 : threeOK 62 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 63}` are good and pairwise different. -/
theorem three_ok_63 : threeOK 63 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 64}` are good and pairwise different. -/
theorem three_ok_64 : threeOK 64 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 65}` are good and pairwise different. -/
theorem three_ok_65 : threeOK 65 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 66}` are good and pairwise different. -/
theorem three_ok_66 : threeOK 66 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 67}` are good and pairwise different. -/
theorem three_ok_67 : threeOK 67 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 68}` are good and pairwise different. -/
theorem three_ok_68 : threeOK 68 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 69}` are good and pairwise different. -/
theorem three_ok_69 : threeOK 69 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 70}` are good and pairwise different. -/
theorem three_ok_70 : threeOK 70 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 71}` are good and pairwise different. -/
theorem three_ok_71 : threeOK 71 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 72}` are good and pairwise different. -/
theorem three_ok_72 : threeOK 72 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 73}` are good and pairwise different. -/
theorem three_ok_73 : threeOK 73 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 74}` are good and pairwise different. -/
theorem three_ok_74 : threeOK 74 = true := by decide +kernel
/-- Three of the tabulated partitions of `{1, …, 76}` are good and pairwise different. -/
theorem three_ok_76 : threeOK 76 = true := by decide +kernel

/-! ### The tabulated partitions at the twenty values with an exact count -/

/-- The partition tabulated at `1` is a good partition of `{1, …, 1}`. -/
theorem one_ok_1 : oneOK 1 = true := by decide +kernel
/-- The partition tabulated at `2` is a good partition of `{1, …, 2}`. -/
theorem one_ok_2 : oneOK 2 = true := by decide +kernel
/-- The partition tabulated at `3` is a good partition of `{1, …, 3}`. -/
theorem one_ok_3 : oneOK 3 = true := by decide +kernel
/-- The partition tabulated at `4` is a good partition of `{1, …, 4}`. -/
theorem one_ok_4 : oneOK 4 = true := by decide +kernel
/-- The partition tabulated at `5` is a good partition of `{1, …, 5}`. -/
theorem one_ok_5 : oneOK 5 = true := by decide +kernel
/-- The partition tabulated at `7` is a good partition of `{1, …, 7}`. -/
theorem one_ok_7 : oneOK 7 = true := by decide +kernel
/-- The partition tabulated at `8` is a good partition of `{1, …, 8}`. -/
theorem one_ok_8 : oneOK 8 = true := by decide +kernel
/-- The partition tabulated at `9` is a good partition of `{1, …, 9}`. -/
theorem one_ok_9 : oneOK 9 = true := by decide +kernel
/-- The partition tabulated at `10` is a good partition of `{1, …, 10}`. -/
theorem one_ok_10 : oneOK 10 = true := by decide +kernel
/-- The partition tabulated at `11` is a good partition of `{1, …, 11}`. -/
theorem one_ok_11 : oneOK 11 = true := by decide +kernel
/-- The partition tabulated at `12` is a good partition of `{1, …, 12}`. -/
theorem one_ok_12 : oneOK 12 = true := by decide +kernel
/-- The partition tabulated at `14` is a good partition of `{1, …, 14}`. -/
theorem one_ok_14 : oneOK 14 = true := by decide +kernel
/-- The partition tabulated at `23` is a good partition of `{1, …, 23}`. -/
theorem one_ok_23 : oneOK 23 = true := by decide +kernel
/-- The partition tabulated at `30` is a good partition of `{1, …, 30}`. -/
theorem one_ok_30 : oneOK 30 = true := by decide +kernel
/-- The partition tabulated at `32` is a good partition of `{1, …, 32}`. -/
theorem one_ok_32 : oneOK 32 = true := by decide +kernel
/-- The partition tabulated at `86` is a good partition of `{1, …, 86}`. -/
theorem one_ok_86 : oneOK 86 = true := by decide +kernel

/-- The two partitions tabulated at `6` are good and different. -/
theorem two_ok_6 : twoOK 6 = true := by decide +kernel
/-- The two partitions tabulated at `13` are good and different. -/
theorem two_ok_13 : twoOK 13 = true := by decide +kernel
/-- The two partitions tabulated at `21` are good and different. -/
theorem two_ok_21 : twoOK 21 = true := by decide +kernel
/-- The two partitions tabulated at `75` are good and different. -/
theorem two_ok_75 : twoOK 75 = true := by decide +kernel

/-! ### The exhaustive search at the twenty values with an exact count -/

/-- Every good partition of `{1, …, 1}` is one of the tabulated ones. -/
theorem search_1 : search 1 (baseWitnesses 1) = true := by decide +kernel
/-- Every good partition of `{1, …, 2}` is one of the tabulated ones. -/
theorem search_2 : search 2 (baseWitnesses 2) = true := by decide +kernel
/-- Every good partition of `{1, …, 3}` is one of the tabulated ones. -/
theorem search_3 : search 3 (baseWitnesses 3) = true := by decide +kernel
/-- Every good partition of `{1, …, 4}` is one of the tabulated ones. -/
theorem search_4 : search 4 (baseWitnesses 4) = true := by decide +kernel
/-- Every good partition of `{1, …, 5}` is one of the tabulated ones. -/
theorem search_5 : search 5 (baseWitnesses 5) = true := by decide +kernel
/-- Every good partition of `{1, …, 6}` is one of the tabulated ones. -/
theorem search_6 : search 6 (baseWitnesses 6) = true := by decide +kernel
/-- Every good partition of `{1, …, 7}` is one of the tabulated ones. -/
theorem search_7 : search 7 (baseWitnesses 7) = true := by decide +kernel
/-- Every good partition of `{1, …, 8}` is one of the tabulated ones. -/
theorem search_8 : search 8 (baseWitnesses 8) = true := by decide +kernel
/-- Every good partition of `{1, …, 9}` is one of the tabulated ones. -/
theorem search_9 : search 9 (baseWitnesses 9) = true := by decide +kernel
/-- Every good partition of `{1, …, 10}` is one of the tabulated ones. -/
theorem search_10 : search 10 (baseWitnesses 10) = true := by decide +kernel
/-- Every good partition of `{1, …, 11}` is one of the tabulated ones. -/
theorem search_11 : search 11 (baseWitnesses 11) = true := by decide +kernel
/-- Every good partition of `{1, …, 12}` is one of the tabulated ones. -/
theorem search_12 : search 12 (baseWitnesses 12) = true := by decide +kernel
/-- Every good partition of `{1, …, 13}` is one of the tabulated ones. -/
theorem search_13 : search 13 (baseWitnesses 13) = true := by decide +kernel
/-- Every good partition of `{1, …, 14}` is one of the tabulated ones. -/
theorem search_14 : search 14 (baseWitnesses 14) = true := by decide +kernel
/-- Every good partition of `{1, …, 21}` is one of the tabulated ones. -/
theorem search_21 : search 21 (baseWitnesses 21) = true := by decide +kernel
/-- Every good partition of `{1, …, 23}` is one of the tabulated ones. -/
theorem search_23 : search 23 (baseWitnesses 23) = true := by decide +kernel
/-- Every good partition of `{1, …, 30}` is one of the tabulated ones. -/
theorem search_30 : search 30 (baseWitnesses 30) = true := by decide +kernel
/-- Every good partition of `{1, …, 32}` is one of the tabulated ones. -/
theorem search_32 : search 32 (baseWitnesses 32) = true := by decide +kernel
/-- Every good partition of `{1, …, 75}` is one of the tabulated ones. -/
theorem search_75 : search 75 (baseWitnesses 75) = true := by decide +kernel
/-- Every good partition of `{1, …, 86}` is one of the tabulated ones. -/
theorem search_86 : search 86 (baseWitnesses 86) = true := by decide +kernel

/-! ### The same facts in the shape the exact counts consume -/

/-- The tabulated partition is the only good partition of `{1, …, 1}`. -/
theorem search_one_1 : search 1 [wAt 1 0] = true :=
  (congrArg (search 1) (rfl : [wAt 1 0] = baseWitnesses 1)).trans search_1
/-- The tabulated partition is the only good partition of `{1, …, 2}`. -/
theorem search_one_2 : search 2 [wAt 2 0] = true :=
  (congrArg (search 2) (rfl : [wAt 2 0] = baseWitnesses 2)).trans search_2
/-- The tabulated partition is the only good partition of `{1, …, 3}`. -/
theorem search_one_3 : search 3 [wAt 3 0] = true :=
  (congrArg (search 3) (rfl : [wAt 3 0] = baseWitnesses 3)).trans search_3
/-- The tabulated partition is the only good partition of `{1, …, 4}`. -/
theorem search_one_4 : search 4 [wAt 4 0] = true :=
  (congrArg (search 4) (rfl : [wAt 4 0] = baseWitnesses 4)).trans search_4
/-- The tabulated partition is the only good partition of `{1, …, 5}`. -/
theorem search_one_5 : search 5 [wAt 5 0] = true :=
  (congrArg (search 5) (rfl : [wAt 5 0] = baseWitnesses 5)).trans search_5
/-- The tabulated partition is the only good partition of `{1, …, 7}`. -/
theorem search_one_7 : search 7 [wAt 7 0] = true :=
  (congrArg (search 7) (rfl : [wAt 7 0] = baseWitnesses 7)).trans search_7
/-- The tabulated partition is the only good partition of `{1, …, 8}`. -/
theorem search_one_8 : search 8 [wAt 8 0] = true :=
  (congrArg (search 8) (rfl : [wAt 8 0] = baseWitnesses 8)).trans search_8
/-- The tabulated partition is the only good partition of `{1, …, 9}`. -/
theorem search_one_9 : search 9 [wAt 9 0] = true :=
  (congrArg (search 9) (rfl : [wAt 9 0] = baseWitnesses 9)).trans search_9
/-- The tabulated partition is the only good partition of `{1, …, 10}`. -/
theorem search_one_10 : search 10 [wAt 10 0] = true :=
  (congrArg (search 10) (rfl : [wAt 10 0] = baseWitnesses 10)).trans search_10
/-- The tabulated partition is the only good partition of `{1, …, 11}`. -/
theorem search_one_11 : search 11 [wAt 11 0] = true :=
  (congrArg (search 11) (rfl : [wAt 11 0] = baseWitnesses 11)).trans search_11
/-- The tabulated partition is the only good partition of `{1, …, 12}`. -/
theorem search_one_12 : search 12 [wAt 12 0] = true :=
  (congrArg (search 12) (rfl : [wAt 12 0] = baseWitnesses 12)).trans search_12
/-- The tabulated partition is the only good partition of `{1, …, 14}`. -/
theorem search_one_14 : search 14 [wAt 14 0] = true :=
  (congrArg (search 14) (rfl : [wAt 14 0] = baseWitnesses 14)).trans search_14
/-- The tabulated partition is the only good partition of `{1, …, 23}`. -/
theorem search_one_23 : search 23 [wAt 23 0] = true :=
  (congrArg (search 23) (rfl : [wAt 23 0] = baseWitnesses 23)).trans search_23
/-- The tabulated partition is the only good partition of `{1, …, 30}`. -/
theorem search_one_30 : search 30 [wAt 30 0] = true :=
  (congrArg (search 30) (rfl : [wAt 30 0] = baseWitnesses 30)).trans search_30
/-- The tabulated partition is the only good partition of `{1, …, 32}`. -/
theorem search_one_32 : search 32 [wAt 32 0] = true :=
  (congrArg (search 32) (rfl : [wAt 32 0] = baseWitnesses 32)).trans search_32
/-- The tabulated partition is the only good partition of `{1, …, 86}`. -/
theorem search_one_86 : search 86 [wAt 86 0] = true :=
  (congrArg (search 86) (rfl : [wAt 86 0] = baseWitnesses 86)).trans search_86

/-- The two tabulated partitions are the only good partitions of `{1, …, 6}`. -/
theorem search_two_6 : search 6 [wAt 6 0, wAt 6 1] = true :=
  (congrArg (search 6) (rfl : [wAt 6 0, wAt 6 1] = baseWitnesses 6)).trans search_6
/-- The two tabulated partitions are the only good partitions of `{1, …, 13}`. -/
theorem search_two_13 : search 13 [wAt 13 0, wAt 13 1] = true :=
  (congrArg (search 13) (rfl : [wAt 13 0, wAt 13 1] = baseWitnesses 13)).trans search_13
/-- The two tabulated partitions are the only good partitions of `{1, …, 21}`. -/
theorem search_two_21 : search 21 [wAt 21 0, wAt 21 1] = true :=
  (congrArg (search 21) (rfl : [wAt 21 0, wAt 21 1] = baseWitnesses 21)).trans search_21
/-- The two tabulated partitions are the only good partitions of `{1, …, 75}`. -/
theorem search_two_75 : search 75 [wAt 75 0, wAt 75 1] = true :=
  (congrArg (search 75) (rfl : [wAt 75 0, wAt 75 1] = baseWitnesses 75)).trans search_75

end GNM

import GNM.Basic
import GNM.SearchDefs

/-!
# From the Boolean checkers to good partitions

Explicit partitions and explicit zero-sum frames are carried as lists of lists of numbers, and the
Boolean functions of `GNM.SearchDefs` decide their defining properties. This module is the bridge:
each checker is paired with a theorem saying that a list passing it names a good partition,
respectively a partition into zero-sum triples, of the intended set, and that two lists one of whose
blocks the other does not have name different partitions. Nothing here is evaluated; the kernel
computations live in a module that imports no library at all.

The functions of `GNM.SearchDefs` are written with explicit recursors, so the first group of
theorems below restates each of them in the language of lists — membership, length, sum,
repetition — and the rest of the development uses only those restatements.
-/

namespace GNM

open GN

/-! ### Conjunctions and disjunctions folded over a list -/

/-- The left half of a true conjunction of Booleans is true. -/
theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => exact h

/-- The right half of a true conjunction of Booleans is true. -/
theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => exact Bool.noConfusion h

/-- A test folded over a list with conjunction is true exactly when it holds of every entry. -/
theorem foldAnd_iff {α : Type*} {f : α → Bool} {l : List α} :
    (List.rec (motive := fun _ => Bool) true (fun a _ ih => f a && ih) l) = true ↔
      ∀ a ∈ l, f a = true := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have e : (List.rec (motive := fun _ => Bool) true (fun a _ ih => f a && ih) (a :: t)) =
          (f a && (List.rec (motive := fun _ => Bool) true (fun a _ ih => f a && ih) t)) := rfl
      rw [e, Bool.and_eq_true, ih]
      simp

/-- A test folded over a list with disjunction is true exactly when it holds of some entry. -/
theorem foldOr_iff {α : Type*} {f : α → Bool} {l : List α} :
    (List.rec (motive := fun _ => Bool) false (fun a _ ih => f a || ih) l) = true ↔
      ∃ a ∈ l, f a = true := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have e : (List.rec (motive := fun _ => Bool) false (fun a _ ih => f a || ih) (a :: t)) =
          (f a || (List.rec (motive := fun _ => Bool) false (fun a _ ih => f a || ih) t)) := rfl
      rw [e, Bool.or_eq_true, ih]
      simp

/-! ### The checkers on lists of natural numbers -/

/-- The occurrence test is correct. -/
theorem memList_iff {y : ℕ} {l : List ℕ} : memList y l = true ↔ y ∈ l := by
  have e : memList y l =
      (List.rec (motive := fun _ => Bool) false (fun z _ ih => Nat.beq y z || ih) l) := rfl
  rw [e, foldOr_iff (f := fun z => Nat.beq y z)]
  simp

/-- The occurrence test fails exactly when the number does not occur. -/
theorem memList_eq_false {y : ℕ} {l : List ℕ} : memList y l = false ↔ y ∉ l := by
  rw [Bool.eq_false_iff, ne_eq, memList_iff]

/-- A test holds of every block of a list of blocks exactly when the folded test is true. -/
theorem allB_iff {f : List ℕ → Bool} {l : List (List ℕ)} :
    allB f l = true ↔ ∀ b ∈ l, f b = true := foldAnd_iff

/-- A test holds of every entry of a list exactly when the folded test is true. -/
theorem allNat_iff {f : ℕ → Bool} {l : List ℕ} :
    allNat f l = true ↔ ∀ y ∈ l, f y = true := foldAnd_iff

/-- The appending function is concatenation. -/
theorem appList_eq (l r : List ℕ) : appList l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have e : appList (a :: t) r = a :: appList t r := rfl
      rw [e, ih, List.cons_append]

/-- The length function is the length of the list. -/
theorem lenList_eq (l : List ℕ) : lenList l = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have e : lenList (a :: t) = lenList t + 1 := rfl
      rw [e, ih, List.length_cons]

/-- The sum function is the sum of the list. -/
theorem sumList_eq (l : List ℕ) : sumList l = l.sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have e : sumList (a :: t) = a + sumList t := rfl
      rw [e, ih, List.sum_cons]

/-- The flattening function is the concatenation of the blocks. -/
theorem flat_eq (bs : List (List ℕ)) : flat bs = bs.flatten := by
  induction bs with
  | nil => rfl
  | cons b t ih =>
      have e : flat (b :: t) = appList b (flat t) := rfl
      rw [e, appList_eq, ih, List.flatten_cons]

/-- The repetition test is correct. -/
theorem noDup_iff {l : List ℕ} : noDup l = true ↔ l.Nodup := by
  induction l with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons a t ih =>
      have e : noDup (a :: t) = (!memList a t && noDup t) := rfl
      rw [e, Bool.and_eq_true, ih, List.nodup_cons]
      simp [memList_eq_false]

/-- The range test is correct. -/
theorem inRange_iff {n : ℕ} {l : List ℕ} : inRange n l = true ↔ ∀ y ∈ l, 1 ≤ y ∧ y ≤ n := by
  have e : inRange n l = (List.rec (motive := fun _ => Bool) true
      (fun y _ ih => (Nat.ble 1 y && Nat.ble y n) && ih) l) := rfl
  rw [e, foldAnd_iff (f := fun y => Nat.ble 1 y && Nat.ble y n)]
  simp [Bool.and_eq_true, Nat.ble_eq]

/-- A number the power-of-three test accepts is a power of three. -/
theorem pow3_of_isPow3 {n : ℕ} (h : isPow3 n = true) : ∃ k : ℕ, n = 3 ^ k := by
  simp only [isPow3, Bool.or_eq_true, Nat.beq_eq] at h
  have h7 : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 ∨ n = 81 ∨ n = 243 ∨ n = 729 := by tauto
  rcases h7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨3, by norm_num⟩
  · exact ⟨4, by norm_num⟩
  · exact ⟨5, by norm_num⟩
  · exact ⟨6, by norm_num⟩

/-- The power-of-three test is correct for every value it can be applied to in this development:
a block sum of an interval below the seventh power of three. -/
theorem isPow3_iff {n : ℕ} (hn : n ≤ 729) : isPow3 n = true ↔ ∃ k : ℕ, n = 3 ^ k := by
  refine ⟨fun h => pow3_of_isPow3 h, ?_⟩
  rintro ⟨k, rfl⟩
  have hk : k ≤ 6 := by
    by_contra hk
    have h7 : (3 : ℕ) ^ 7 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h8 := le_trans h7 hn
    norm_num at h8
  interval_cases k <;> decide

/-- The block checker is exactly the three conditions on a block. -/
theorem goodBlock_iff {b : List ℕ} :
    goodBlock b = true ↔ b ≠ [] ∧ b.length ≤ 3 ∧ isPow3 b.sum = true := by
  cases b with
  | nil => simp [goodBlock]
  | cons x t =>
      have e : goodBlock (x :: t) = (Nat.ble (lenList (x :: t)) 3 && isPow3 (sumList (x :: t))) :=
        rfl
      rw [e, Bool.and_eq_true, lenList_eq, sumList_eq, Nat.ble_eq]
      simp

/-- Two blocks pass the equality test exactly when they have the same length and the entries of the
first all occur in the second. -/
theorem sameBlock_iff {b c : List ℕ} :
    sameBlock b c = true ↔ b.length = c.length ∧ ∀ y ∈ b, y ∈ c := by
  have e : sameBlock b c = (Nat.beq (lenList b) (lenList c) && allNat (fun y => memList y c) b) :=
    rfl
  rw [e, Bool.and_eq_true, allNat_iff, Nat.beq_eq, lenList_eq, lenList_eq]
  simp [memList_iff]

/-- Some block of the second list has the same entries as the first argument. -/
private noncomputable def matchesSome (b : List ℕ) (cs : List (List ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun c _ jh => sameBlock b c || jh) cs

/-- The matching test is correct. -/
private theorem matchesSome_iff {b : List ℕ} {cs : List (List ℕ)} :
    matchesSome b cs = true ↔ ∃ c ∈ cs, sameBlock b c = true :=
  foldOr_iff (f := fun c => sameBlock b c)

/-- A block matches no block of the second list exactly when the matching test fails. -/
private theorem matchesSome_eq_false {b : List ℕ} {cs : List (List ℕ)} :
    matchesSome b cs = false ↔ ∀ c ∈ cs, sameBlock b c = false := by
  rw [Bool.eq_false_iff, ne_eq, matchesSome_iff]
  simp

/-- The difference test is correct: it holds exactly when some block of the first list matches no
block of the second. -/
theorem differ_iff {bs cs : List (List ℕ)} :
    differ bs cs = true ↔ ∃ b ∈ bs, ∀ c ∈ cs, sameBlock b c = false := by
  have e : differ bs cs = (List.rec (motive := fun _ => Bool) false
      (fun b _ ih => (!matchesSome b cs) || ih) bs) := rfl
  rw [e, foldOr_iff (f := fun b => !matchesSome b cs)]
  simp only [Bool.not_eq_true', matchesSome_eq_false]

/-! ### Blocks inside a concatenation without repetition -/

/-- A block of a list of blocks whose concatenation has no repeated entry has no repeated entry. -/
theorem nodup_of_flatten_nodup {α : Type*} {b : List α} :
    ∀ bs : List (List α), bs.flatten.Nodup → b ∈ bs → b.Nodup := by
  intro bs
  induction bs with
  | nil => intro _ hb; simp at hb
  | cons a t ih =>
      intro h hb
      rw [List.flatten_cons, List.nodup_append] at h
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact h.1
      · exact ih h.2.1 hb'

/-- Two different blocks of a list of blocks whose concatenation has no repeated entry share no
entry. -/
theorem not_mem_of_flatten_nodup {α : Type*} {b c : List α} {y : α} (hbc : b ≠ c) (hy : y ∈ b) :
    ∀ bs : List (List α), bs.flatten.Nodup → b ∈ bs → c ∈ bs → y ∉ c := by
  intro bs
  induction bs with
  | nil => intro _ hb _; simp at hb
  | cons a t ih =>
      intro h hb hc
      rw [List.flatten_cons, List.nodup_append] at h
      rcases List.mem_cons.mp hb with rfl | hb'
      · rcases List.mem_cons.mp hc with rfl | hc'
        · exact absurd rfl hbc
        · exact fun hyc => h.2.2 y hy y (List.mem_flatten.mpr ⟨c, hc', hyc⟩) rfl
      · rcases List.mem_cons.mp hc with rfl | hc'
        · exact fun hyc => h.2.2 y hyc y (List.mem_flatten.mpr ⟨b, hb', hy⟩) rfl
        · exact ih h.2.1 hb' hc'

/-! ### The sets named by lists of numbers -/

/-- The set of integers named by a list of numbers. -/
def toBlock (b : List ℕ) : Finset ℤ := (b.map (fun x : ℕ => (x : ℤ))).toFinset

/-- The set of blocks named by a list of lists of numbers. -/
def toBlocks (bs : List (List ℕ)) : Finset (Finset ℤ) := (bs.map toBlock).toFinset

/-- Membership in the set named by a list of numbers. -/
theorem mem_toBlock_iff {x : ℤ} {b : List ℕ} : x ∈ toBlock b ↔ ∃ y ∈ b, (y : ℤ) = x := by
  simp only [toBlock, List.mem_toFinset, List.mem_map]

/-- The set named by a list of numbers contains the image of each entry. -/
theorem mem_toBlock {y : ℕ} {b : List ℕ} (h : y ∈ b) : (y : ℤ) ∈ toBlock b :=
  mem_toBlock_iff.mpr ⟨y, h, rfl⟩

/-- Membership in the set of blocks named by a list of lists of numbers. -/
theorem mem_toBlocks {B : Finset ℤ} {bs : List (List ℕ)} :
    B ∈ toBlocks bs ↔ ∃ b ∈ bs, toBlock b = B := by
  simp [toBlocks]

/-- A list without repetition names as many integers as it has entries. -/
theorem card_toBlock {b : List ℕ} (h : b.Nodup) : (toBlock b).card = b.length := by
  have hm : (b.map (fun x : ℕ => (x : ℤ))).Nodup := h.map (fun _ _ e => by exact_mod_cast e)
  rw [toBlock, List.toFinset_card_of_nodup hm, List.length_map]

/-- The sum of the integers a list without repetition names is the sum of its entries. -/
theorem sum_toBlock {b : List ℕ} (h : b.Nodup) : (toBlock b).sum id = (b.sum : ℤ) := by
  have hm : (b.map (fun x : ℕ => (x : ℤ))).Nodup := h.map (fun _ _ e => by exact_mod_cast e)
  rw [toBlock, List.sum_toFinset _ hm, List.map_id]
  exact (Nat.cast_list_sum b).symm

/-- An entry of a block occurs in the concatenation of the blocks. -/
theorem mem_flat {y : ℕ} {bs : List (List ℕ)} : y ∈ flat bs ↔ ∃ b ∈ bs, y ∈ b := by
  rw [flat_eq, List.mem_flatten]

/-! ### The partition checker -/

/-- The four facts the partition checker establishes. -/
theorem checkPartition_facts {n : ℕ} {bs : List (List ℕ)} (h : checkPartition n bs = true) :
    (∀ b ∈ bs, goodBlock b = true) ∧ (flat bs).Nodup ∧ (flat bs).length = n ∧
      ∀ y ∈ flat bs, 1 ≤ y ∧ y ≤ n := by
  have e : (allB goodBlock bs && (noDup (flat bs) && Nat.beq (lenList (flat bs)) n &&
      inRange n (flat bs))) = true := h
  have h1 := bool_and_left e
  have e2 := bool_and_right e
  have h2 := bool_and_left (bool_and_left e2)
  have h3 := bool_and_right (bool_and_left e2)
  have h4 := bool_and_right e2
  refine ⟨allB_iff.mp h1, noDup_iff.mp h2, ?_, inRange_iff.mp h4⟩
  have h5 := Nat.eq_of_beq_eq_true h3
  rwa [lenList_eq] at h5

/-- Each block of a checked partition has no repeated entry. -/
theorem nodup_of_checkPartition {n : ℕ} {bs : List (List ℕ)} (h : checkPartition n bs = true)
    {b : List ℕ} (hb : b ∈ bs) : b.Nodup := by
  have hnd := (checkPartition_facts h).2.1
  rw [flat_eq] at hnd
  exact nodup_of_flatten_nodup bs hnd hb

/-- The entries of a checked partition are exactly the numbers of the interval. -/
theorem toFinset_flat {n : ℕ} {bs : List (List ℕ)} (h : checkPartition n bs = true) :
    (flat bs).toFinset = Finset.Icc 1 n := by
  obtain ⟨-, hnd, hlen, hr⟩ := checkPartition_facts h
  have hsub : (flat bs).toFinset ⊆ Finset.Icc 1 n := by
    intro y hy
    exact Finset.mem_Icc.mpr (hr y (List.mem_toFinset.mp hy))
  have hIcc : (Finset.Icc 1 n).card = n := by simp
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [List.toFinset_card_of_nodup hnd, hlen, hIcc]

/-- A list that passes the partition checker names a good partition of the interval. -/
theorem isGoodPartition_of_checkPartition {n : ℕ} {bs : List (List ℕ)}
    (h : checkPartition n bs = true) : IsGoodPartition n (toBlocks bs) := by
  obtain ⟨hg, hnd, hlen, hr⟩ := checkPartition_facts h
  have hset := toFinset_flat h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨B, hB, hxB⟩
      obtain ⟨b, hb, rfl⟩ := mem_toBlocks.mp hB
      obtain ⟨y, hy, rfl⟩ := mem_toBlock_iff.mp hxB
      obtain ⟨hy1, hy2⟩ := hr y (mem_flat.mpr ⟨b, hb, hy⟩)
      exact ⟨by exact_mod_cast hy1, by exact_mod_cast hy2⟩
    · rintro ⟨hx1, hx2⟩
      have hxn : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by omega)
      have hmem : x.toNat ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [← hset, List.mem_toFinset] at hmem
      obtain ⟨b, hb, hyb⟩ := mem_flat.mp hmem
      exact ⟨toBlock b, mem_toBlocks.mpr ⟨b, hb, rfl⟩, by rw [← hxn]; exact mem_toBlock hyb⟩
  · intro B hB C hC hBC
    obtain ⟨b, hb, rfl⟩ := mem_toBlocks.mp hB
    obtain ⟨c, hc, rfl⟩ := mem_toBlocks.mp hC
    have hbc : b ≠ c := fun e => hBC (by rw [e])
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := mem_toBlock_iff.mp hx
    obtain ⟨z, hz, hzy⟩ := mem_toBlock_iff.mp hx'
    have hzy' : z = y := by exact_mod_cast hzy
    rw [flat_eq] at hnd
    exact not_mem_of_flatten_nodup hbc hy bs hnd hb hc (hzy' ▸ hz)
  · intro B hB
    obtain ⟨b, hb, rfl⟩ := mem_toBlocks.mp hB
    obtain ⟨hne, hlen3, hp3⟩ := goodBlock_iff.mp (hg b hb)
    have hbnd : b.Nodup := nodup_of_checkPartition h hb
    obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨⟨(y : ℤ), mem_toBlock List.mem_cons_self⟩, ?_, ?_⟩
    · rw [card_toBlock hbnd]
      exact hlen3
    · obtain ⟨k, hk⟩ := pow3_of_isPow3 hp3
      refine ⟨k, ?_⟩
      rw [sum_toBlock hbnd, hk]
      push_cast
      ring

/-- Two checked lists, one of which has a block the other has not, name different partitions. -/
theorem toBlocks_ne_of_differ {n : ℕ} {bs cs : List (List ℕ)} (hb : checkPartition n bs = true)
    (hc : checkPartition n cs = true) (h : differ bs cs = true) : toBlocks bs ≠ toBlocks cs := by
  intro heq
  obtain ⟨b, hbs, hnm⟩ := differ_iff.mp h
  have hmem : toBlock b ∈ toBlocks cs := heq ▸ mem_toBlocks.mpr ⟨b, hbs, rfl⟩
  obtain ⟨c, hcs, hbc⟩ := mem_toBlocks.mp hmem
  have hbnd : b.Nodup := nodup_of_checkPartition hb hbs
  have hcnd : c.Nodup := nodup_of_checkPartition hc hcs
  have hlen : b.length = c.length := by
    rw [← card_toBlock hbnd, ← card_toBlock hcnd, hbc]
  have hsub : ∀ y ∈ b, y ∈ c := by
    intro y hy
    have hyc : (y : ℤ) ∈ toBlock c := by rw [hbc]; exact mem_toBlock hy
    obtain ⟨z, hz, hzy⟩ := mem_toBlock_iff.mp hyc
    have hzy' : z = y := by exact_mod_cast hzy
    exact hzy' ▸ hz
  have hsb := sameBlock_iff.mpr ⟨hlen, hsub⟩
  rw [hnm c hcs] at hsb
  exact Bool.noConfusion hsb

/-- Three checked lists, pairwise differing, give a count of at least three. -/
theorem three_le_count_of_witnesses {n : ℕ} {w₁ w₂ w₃ : List (List ℕ)}
    (h₁ : checkPartition n w₁ = true) (h₂ : checkPartition n w₂ = true)
    (h₃ : checkPartition n w₃ = true) (d₁₂ : differ w₁ w₂ = true) (d₁₃ : differ w₁ w₃ = true)
    (d₂₃ : differ w₂ w₃ = true) : 3 ≤ count n :=
  three_le_count (isGoodPartition_of_checkPartition h₁) (isGoodPartition_of_checkPartition h₂)
    (isGoodPartition_of_checkPartition h₃) (toBlocks_ne_of_differ h₁ h₂ d₁₂)
    (toBlocks_ne_of_differ h₁ h₃ d₁₃) (toBlocks_ne_of_differ h₂ h₃ d₂₃)

/-! ### The checkers on lists of integers -/

/-- The occurrence test on integers is correct. -/
theorem memListZ_iff {y : ℤ} {l : List ℤ} : memListZ y l = true ↔ y ∈ l := by
  have e : memListZ y l =
      (List.rec (motive := fun _ => Bool) false (fun z _ ih => (y == z) || ih) l) := rfl
  rw [e, foldOr_iff (f := fun z => (y == z))]
  simp

/-- The occurrence test on integers fails exactly when the integer does not occur. -/
theorem memListZ_eq_false {y : ℤ} {l : List ℤ} : memListZ y l = false ↔ y ∉ l := by
  rw [Bool.eq_false_iff, ne_eq, memListZ_iff]

/-- The length function on integer lists is the length of the list. -/
theorem lenListZ_eq (l : List ℤ) : lenListZ l = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have e : lenListZ (a :: t) = lenListZ t + 1 := rfl
      rw [e, ih, List.length_cons]

/-- The sum function on integer lists is the sum of the list. -/
theorem sumListZ_eq (l : List ℤ) : sumListZ l = l.sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have e : sumListZ (a :: t) = a + sumListZ t := rfl
      rw [e, ih, List.sum_cons]

/-- The repetition test on integer lists is correct. -/
theorem noDupZ_iff {l : List ℤ} : noDupZ l = true ↔ l.Nodup := by
  induction l with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons a t ih =>
      have e : noDupZ (a :: t) = (!memListZ a t && noDupZ t) := rfl
      rw [e, Bool.and_eq_true, ih, List.nodup_cons]
      simp [memListZ_eq_false]

/-- A list built on the front of another list is their concatenation. -/
private theorem consAll_eq (r : List ℤ) (l : List ℤ) :
    (List.rec (motive := fun _ => List ℤ) r (fun y _ jh => y :: jh) l) = l ++ r := by
  induction l with
  | nil => rfl
  | cons a s ih =>
      have e : (List.rec (motive := fun _ => List ℤ) r (fun y _ jh => y :: jh) (a :: s)) =
          a :: (List.rec (motive := fun _ => List ℤ) r (fun y _ jh => y :: jh) s) := rfl
      rw [e, ih, List.cons_append]

/-- The flattening function on integer blocks is the concatenation of the blocks. -/
theorem flatZ_eq (bs : List (List ℤ)) : flatZ bs = bs.flatten := by
  induction bs with
  | nil => rfl
  | cons b t ih =>
      have e : flatZ (b :: t) =
          (List.rec (motive := fun _ => List ℤ) (flatZ t) (fun y _ jh => y :: jh) b) := rfl
      rw [e, consAll_eq, ih, List.flatten_cons]

/-- An entry of an integer block occurs in the concatenation of the blocks. -/
theorem mem_flatZ {y : ℤ} {bs : List (List ℤ)} : y ∈ flatZ bs ↔ ∃ b ∈ bs, y ∈ b := by
  rw [flatZ_eq, List.mem_flatten]

/-- The zero-sum triple test is correct. -/
theorem zeroTripleOK_iff {b : List ℤ} :
    zeroTripleOK b = true ↔ b.length = 3 ∧ b.Nodup ∧ b.sum = 0 := by
  have e : zeroTripleOK b = (Nat.beq (lenListZ b) 3 && noDupZ b && (sumListZ b == 0)) := rfl
  rw [e, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenListZ_eq, noDupZ_iff, sumListZ_eq,
    beq_iff_eq]
  exact ⟨fun hx => ⟨hx.1.1, hx.1.2, hx.2⟩, fun hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩⟩

/-- Two integer blocks pass the equality test exactly when they have the same length and the
entries of the first all occur in the second. -/
theorem sameBlockZ_iff {b c : List ℤ} :
    sameBlockZ b c = true ↔ b.length = c.length ∧ ∀ y ∈ b, y ∈ c := by
  have e : sameBlockZ b c = (Nat.beq (lenListZ b) (lenListZ c) &&
      (List.rec (motive := fun _ => Bool) true (fun y _ ih => memListZ y c && ih) b)) := rfl
  rw [e, Bool.and_eq_true, foldAnd_iff (f := fun y => memListZ y c), Nat.beq_eq, lenListZ_eq,
    lenListZ_eq]
  simp [memListZ_iff]

/-- Some integer block of the second list has the same entries as the first argument. -/
private noncomputable def matchesSomeZ (b : List ℤ) (cs : List (List ℤ)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun c _ jh => sameBlockZ b c || jh) cs

/-- The matching test on integer blocks is correct. -/
private theorem matchesSomeZ_iff {b : List ℤ} {cs : List (List ℤ)} :
    matchesSomeZ b cs = true ↔ ∃ c ∈ cs, sameBlockZ b c = true :=
  foldOr_iff (f := fun c => sameBlockZ b c)

/-- An integer block matches no block of the second list exactly when the test fails. -/
private theorem matchesSomeZ_eq_false {b : List ℤ} {cs : List (List ℤ)} :
    matchesSomeZ b cs = false ↔ ∀ c ∈ cs, sameBlockZ b c = false := by
  rw [Bool.eq_false_iff, ne_eq, matchesSomeZ_iff]
  simp

/-- The difference test on integer blocks is correct. -/
theorem differZ_iff {bs cs : List (List ℤ)} :
    differZ bs cs = true ↔ ∃ b ∈ bs, ∀ c ∈ cs, sameBlockZ b c = false := by
  have e : differZ bs cs = (List.rec (motive := fun _ => Bool) false
      (fun b _ ih => (!matchesSomeZ b cs) || ih) bs) := rfl
  rw [e, foldOr_iff (f := fun b => !matchesSomeZ b cs)]
  simp only [Bool.not_eq_true', matchesSomeZ_eq_false]

/-! ### The sets named by lists of integers -/

/-- The set of integers named by a list of integers. -/
def toBlockZ (b : List ℤ) : Finset ℤ := b.toFinset

/-- The set of triples named by a list of lists of integers. -/
def toBlocksZ (bs : List (List ℤ)) : Finset (Finset ℤ) := (bs.map toBlockZ).toFinset

/-- Membership in the set of triples named by a list of lists of integers. -/
theorem mem_toBlocksZ {B : Finset ℤ} {bs : List (List ℤ)} :
    B ∈ toBlocksZ bs ↔ ∃ b ∈ bs, toBlockZ b = B := by
  simp [toBlocksZ]

/-- The four facts the frame checker establishes. -/
theorem framesOK_facts {support : List ℤ} {bs : List (List ℤ)} (h : framesOK support bs = true) :
    (∀ b ∈ bs, zeroTripleOK b = true) ∧ (flatZ bs).Nodup ∧
      (flatZ bs).length = support.length ∧ ∀ y ∈ flatZ bs, y ∈ support := by
  have e : ((List.rec (motive := fun _ => Bool) true (fun b _ ih => zeroTripleOK b && ih) bs) &&
      (noDupZ (flatZ bs) && Nat.beq (lenListZ (flatZ bs)) (lenListZ support) &&
        (List.rec (motive := fun _ => Bool) true
          (fun y _ ih => memListZ y support && ih) (flatZ bs)))) = true := h
  have h1 := bool_and_left e
  have e2 := bool_and_right e
  have h2 := bool_and_left (bool_and_left e2)
  have h3 := bool_and_right (bool_and_left e2)
  have h4 := bool_and_right e2
  refine ⟨foldAnd_iff.mp h1, noDupZ_iff.mp h2, ?_, ?_⟩
  · have h5 := Nat.eq_of_beq_eq_true h3
    rwa [lenListZ_eq, lenListZ_eq] at h5
  · intro y hy
    exact memListZ_iff.mp ((foldAnd_iff (f := fun y => memListZ y support)).mp h4 y hy)

/-- A list that passes the frame checker names a partition of the support into zero-sum triples. -/
theorem zeroPartition_of_framesOK {s : Finset ℤ} {support : List ℤ} (hs : support.toFinset = s)
    (hnd : noDupZ support = true) {bs : List (List ℤ)} (h : framesOK support bs = true) :
    ZeroPartition s (toBlocksZ bs) := by
  obtain ⟨hz, hfnd, hlen, hmem⟩ := framesOK_facts h
  have hsupnd : support.Nodup := noDupZ_iff.mp hnd
  have hflat : (flatZ bs).toFinset = s := by
    have hsub : (flatZ bs).toFinset ⊆ support.toFinset := by
      intro y hy
      exact List.mem_toFinset.mpr (hmem y (List.mem_toFinset.mp hy))
    have hcard : support.toFinset.card ≤ (flatZ bs).toFinset.card := by
      rw [List.toFinset_card_of_nodup hfnd, List.toFinset_card_of_nodup hsupnd, hlen]
    rw [← hs]
    exact Finset.eq_of_subset_of_card_le hsub hcard
  refine ⟨?_, ?_, ?_⟩
  · rw [← hflat]
    ext x
    simp only [Finset.mem_biUnion, id_eq, List.mem_toFinset, mem_flatZ]
    constructor
    · rintro ⟨B, hB, hxB⟩
      obtain ⟨b, hb, rfl⟩ := mem_toBlocksZ.mp hB
      exact ⟨b, hb, List.mem_toFinset.mp hxB⟩
    · rintro ⟨b, hb, hxb⟩
      exact ⟨toBlockZ b, mem_toBlocksZ.mpr ⟨b, hb, rfl⟩, List.mem_toFinset.mpr hxb⟩
  · intro B hB C hC hBC
    obtain ⟨b, hb, rfl⟩ := mem_toBlocksZ.mp hB
    obtain ⟨c, hc, rfl⟩ := mem_toBlocksZ.mp hC
    have hbc : b ≠ c := fun e => hBC (by rw [e])
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [toBlockZ, List.mem_toFinset] at hx hx'
    rw [flatZ_eq] at hfnd
    exact not_mem_of_flatten_nodup hbc hx bs hfnd hb hc hx'
  · intro B hB
    obtain ⟨b, hb, rfl⟩ := mem_toBlocksZ.mp hB
    obtain ⟨hlen3, hbnd, hsum⟩ := zeroTripleOK_iff.mp (hz b hb)
    refine ⟨?_, ?_⟩
    · rw [toBlockZ, List.toFinset_card_of_nodup hbnd, hlen3]
    · rw [toBlockZ, List.sum_toFinset _ hbnd, List.map_id, hsum]

/-- Two checked frames, one of which has a triple the other has not, are different. -/
theorem toBlocksZ_ne_of_differZ {support : List ℤ} {bs cs : List (List ℤ)}
    (hb : framesOK support bs = true) (hc : framesOK support cs = true)
    (h : differZ bs cs = true) : toBlocksZ bs ≠ toBlocksZ cs := by
  intro heq
  obtain ⟨b, hbs, hnm⟩ := differZ_iff.mp h
  have hmem : toBlockZ b ∈ toBlocksZ cs := heq ▸ mem_toBlocksZ.mpr ⟨b, hbs, rfl⟩
  obtain ⟨c, hcs, hbc⟩ := mem_toBlocksZ.mp hmem
  have hbnd : b.Nodup := by
    have hfnd := (framesOK_facts hb).2.1
    rw [flatZ_eq] at hfnd
    exact nodup_of_flatten_nodup bs hfnd hbs
  have hcnd : c.Nodup := by
    have hfnd := (framesOK_facts hc).2.1
    rw [flatZ_eq] at hfnd
    exact nodup_of_flatten_nodup cs hfnd hcs
  have hlen : b.length = c.length := by
    have h1 : b.toFinset.card = c.toFinset.card := by rw [← toBlockZ, ← toBlockZ, hbc]
    rwa [List.toFinset_card_of_nodup hbnd, List.toFinset_card_of_nodup hcnd] at h1
  have hsub : ∀ y ∈ b, y ∈ c := by
    intro y hy
    have hyc : y ∈ toBlockZ c := by
      rw [hbc, toBlockZ, List.mem_toFinset]
      exact hy
    rwa [toBlockZ, List.mem_toFinset] at hyc
  have hsb := sameBlockZ_iff.mpr ⟨hlen, hsub⟩
  rw [hnm c hcs] at hsb
  exact Bool.noConfusion hsb

end GNM

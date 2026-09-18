import GNM.SearchDefs
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

The candidate generator prunes the search: for a block `{x, a, b}` with `1 ≤ b < a < x` the sum lies
strictly between `x + a` and `x + 2a`, so once the power of three `3 ^ k` and the second entry `a`
are fixed, the third entry `b = 3 ^ k − x − a` is determined. Completeness of the generator is the
first theorem below, and it is where the bound on the entries enters: the power-of-three test and
the list of powers the generator scans are the explicit ones below `3 ^ 7`, so the statements carry
the hypothesis that three times the largest entry is below `729`.
-/

namespace GNM

open GN

/-! ### The equations of the recursor-defined functions

Every function the kernel evaluates is written with an explicit recursor. Each equation below is
true by definition, one per constructor; the recursors themselves are not used again.
-/

/-- Nothing occurs in the empty list. -/
private theorem memList_nil (y : ℕ) : memList y [] = false := rfl

/-- Occurrence in a list with a first entry. -/
private theorem memList_cons (y z : ℕ) (l : List ℕ) :
    memList y (z :: l) = (Nat.beq y z || memList y l) := rfl

/-- The occurrence test decides membership. -/
private theorem memList_eq_true {y : ℕ} {l : List ℕ} : memList y l = true ↔ y ∈ l := by
  induction l with
  | nil => simp [memList_nil]
  | cons z t ih => simp [memList_cons, ih]

/-- Removing entries from the empty list. -/
private theorem removeAll_nil (B : List ℕ) : removeAll B [] = [] := rfl

/-- Removing the entries of `B` from a list with a first entry. -/
private theorem removeAll_cons (B : List ℕ) (y : ℕ) (t : List ℕ) :
    removeAll B (y :: t) = (if memList y B then removeAll B t else y :: removeAll B t) := rfl

/-- A universal test over the empty list of blocks holds. -/
private theorem allB_nil (f : List ℕ → Bool) : allB f [] = true := rfl

/-- A universal test over a list of blocks with a first block. -/
private theorem allB_cons (f : List ℕ → Bool) (B : List ℕ) (l : List (List ℕ)) :
    allB f (B :: l) = (f B && allB f l) := rfl

/-- The descending list of the numbers below nothing. -/
private theorem downFrom_zero : downFrom 0 = [] := rfl

/-- The descending list of the numbers up to a successor. -/
private theorem downFrom_succ (m : ℕ) : downFrom (m + 1) = (m + 1) :: downFrom m := rfl

/-- The search with no steps left and nothing to cover accepts exactly the prefixes on the list. -/
private theorem searchAll_zero_nil (e : List (List (List ℕ))) (acc : List (List ℕ)) :
    searchAll e 0 [] acc = e.contains acc.reverse := rfl

/-- The search with no steps left and something still to cover fails. -/
private theorem searchAll_zero_cons (e : List (List (List ℕ))) (x : ℕ) (t : List ℕ)
    (acc : List (List ℕ)) : searchAll e 0 (x :: t) acc = false := rfl

/-- The search with nothing to cover accepts exactly the prefixes on the list. -/
private theorem searchAll_succ_nil (e : List (List (List ℕ))) (f : ℕ) (acc : List (List ℕ)) :
    searchAll e (f + 1) [] acc = e.contains acc.reverse := rfl

/-- One step of the search: it branches over the good blocks containing the largest element. -/
private theorem searchAll_succ_cons (e : List (List (List ℕ))) (f x : ℕ) (t : List ℕ)
    (acc : List (List ℕ)) :
    searchAll e (f + 1) (x :: t) acc
      = allB (fun B => searchAll e f (removeAll B t) (B :: acc)) (candidates x t) := rfl

/-- The powers of three that give a two-element block at `x`, as the generator scans them. -/
private noncomputable def pairLoop (x : ℕ) (l : List ℕ) : List ℕ :=
  List.rec [] (fun P _ ih => if Nat.blt x P && Nat.blt P (x + x) then (P - x) :: ih else ih) l

/-- The partners of `x` come from scanning the powers of three. -/
private theorem pairNeeds_eq (x : ℕ) : pairNeeds x = pairLoop x pow3s := rfl

/-- Scanning no powers of three. -/
private theorem pairLoop_nil (x : ℕ) : pairLoop x [] = [] := rfl

/-- Scanning one more power of three for a partner of `x`. -/
private theorem pairLoop_cons (x P : ℕ) (l : List ℕ) :
    pairLoop x (P :: l)
      = (if Nat.blt x P && Nat.blt P (x + x) then (P - x) :: pairLoop x l else pairLoop x l) :=
  rfl

/-- The powers of three that give a three-element block at `x`, as the generator scans them. -/
private noncomputable def tripLoop (x : ℕ) (l : List ℕ) : List ℕ :=
  List.rec [] (fun P _ ih => if Nat.ble (x + 3) P && Nat.ble (P - x) (x + x) then (P - x) :: ih
    else ih) l

/-- The admissible sums of the two smaller entries come from scanning the powers of three. -/
private theorem tripNeeds_eq (x : ℕ) : tripNeeds x = tripLoop x pow3s := rfl

/-- Scanning no powers of three. -/
private theorem tripLoop_nil (x : ℕ) : tripLoop x [] = [] := rfl

/-- Scanning one more power of three for the sum of the two smaller entries. -/
private theorem tripLoop_cons (x P : ℕ) (l : List ℕ) :
    tripLoop x (P :: l)
      = (if Nat.ble (x + 3) P && Nat.ble (P - x) (x + x) then (P - x) :: tripLoop x l
          else tripLoop x l) := rfl

/-- The three-element candidate blocks with entries `x` and `a`, as the generator scans the
admissible sums. -/
private noncomputable def candTrip (x a : ℕ) (t : List ℕ) (ih : List (List ℕ)) (tn : List ℕ) :
    List (List ℕ) :=
  List.rec ih (fun s _ jh =>
    if Nat.blt a s && Nat.blt s (a + a) && memList (s - a) t then [x, a, s - a] :: jh else jh) tn

/-- The candidates at the empty list: the one-element block, when `x` is itself a power of three. -/
private theorem candidates_nil (x : ℕ) : candidates x [] = (if isPow3 x then [[x]] else []) := rfl

/-- The candidates at a list with a first entry `a`: the pair `{x, a}` when `a` is a partner of `x`,
the triples with second entry `a`, and the candidates from the rest of the list. -/
private theorem candidates_cons (x a : ℕ) (t : List ℕ) :
    candidates x (a :: t)
      = (if memList a (pairNeeds x) then
            [x, a] :: candTrip x a t (candidates x t) (tripNeeds x)
          else candTrip x a t (candidates x t) (tripNeeds x)) := rfl

/-- Scanning no admissible sums. -/
private theorem candTrip_nil (x a : ℕ) (t : List ℕ) (ih : List (List ℕ)) :
    candTrip x a t ih [] = ih := rfl

/-- Scanning one more admissible sum. -/
private theorem candTrip_cons (x a : ℕ) (t : List ℕ) (ih : List (List ℕ)) (s : ℕ) (tn : List ℕ) :
    candTrip x a t ih (s :: tn)
      = (if Nat.blt a s && Nat.blt s (a + a) && memList (s - a) t then
            [x, a, s - a] :: candTrip x a t ih tn
          else candTrip x a t ih tn) := rfl

/-! ### The powers of three the generator scans -/

/-- The powers of three up to `729` are the ones the generator scans. -/
private theorem pow3_mem_pow3s {k : ℕ} (h : 3 ^ k ≤ 729) : 3 ^ k ∈ pow3s := by
  have hk : k ≤ 6 := by
    by_contra hk
    have h7 : 3 ^ 7 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h7
    omega
  interval_cases k <;> simp [pow3s]

/-- The power-of-three test accepts every power of three up to `729`. -/
private theorem isPow3_pow {k : ℕ} (h : 3 ^ k ≤ 729) : isPow3 (3 ^ k) = true := by
  have hk : k ≤ 6 := by
    by_contra hk
    have h7 : 3 ^ 7 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h7
    omega
  interval_cases k <;> decide

/-- A power of three strictly between `x` and `2x` contributes its partner of `x`. -/
private theorem mem_pairLoop {x P : ℕ} {l : List ℕ} (hP : P ∈ l) (h1 : x < P) (h2 : P < x + x) :
    P - x ∈ pairLoop x l := by
  induction l with
  | nil => simp at hP
  | cons Q l ihn =>
    rw [pairLoop_cons]
    rcases List.mem_cons.mp hP with rfl | hP'
    · have hg : (Nat.blt x P && Nat.blt P (x + x)) = true := by
        simp only [Bool.and_eq_true, Nat.blt_eq]
        exact ⟨h1, h2⟩
      rw [if_pos hg]
      simp
    · by_cases hg : (Nat.blt x Q && Nat.blt Q (x + x)) = true
      · rw [if_pos hg]
        exact List.mem_cons_of_mem _ (ihn hP')
      · rw [if_neg hg]
        exact ihn hP'

/-- A power of three at least `x + 3` whose deficit at `x` is at most `2x` contributes that
deficit. -/
private theorem mem_tripLoop {x P : ℕ} {l : List ℕ} (hP : P ∈ l) (h1 : x + 3 ≤ P)
    (h2 : P - x ≤ x + x) : P - x ∈ tripLoop x l := by
  induction l with
  | nil => simp at hP
  | cons Q l ihn =>
    rw [tripLoop_cons]
    rcases List.mem_cons.mp hP with rfl | hP'
    · have hg : (Nat.ble (x + 3) P && Nat.ble (P - x) (x + x)) = true := by
        simp only [Bool.and_eq_true, Nat.ble_eq]
        exact ⟨h1, h2⟩
      rw [if_pos hg]
      simp
    · by_cases hg : (Nat.ble (x + 3) Q && Nat.ble (Q - x) (x + x)) = true
      · rw [if_pos hg]
        exact List.mem_cons_of_mem _ (ihn hP')
      · rw [if_neg hg]
        exact ihn hP'

/-! ### Completeness of the candidate generator -/

/-- Scanning the admissible sums keeps the candidates already found. -/
private theorem mem_candTrip_of_mem {x a : ℕ} {t : List ℕ} {ih : List (List ℕ)} {c : List ℕ}
    (h : c ∈ ih) (tn : List ℕ) : c ∈ candTrip x a t ih tn := by
  induction tn with
  | nil => rwa [candTrip_nil]
  | cons s tn ihn =>
    rw [candTrip_cons]
    by_cases hg : (Nat.blt a s && Nat.blt s (a + a) && memList (s - a) t) = true
    · rw [if_pos hg]
      exact List.mem_cons_of_mem _ ihn
    · rw [if_neg hg]
      exact ihn

/-- A triple whose smaller entries sum to an admissible value is generated. -/
private theorem mem_candTrip {x a b : ℕ} {t : List ℕ} {ih : List (List ℕ)} {tn : List ℕ}
    (hs : a + b ∈ tn) (h1 : 0 < b) (h2 : b < a) (hb : memList b t = true) :
    [x, a, b] ∈ candTrip x a t ih tn := by
  induction tn with
  | nil => simp at hs
  | cons s tn ihn =>
    rw [candTrip_cons]
    rcases List.mem_cons.mp hs with heq | hs'
    · have hsb : s - a = b := by omega
      have hg : (Nat.blt a s && Nat.blt s (a + a) && memList (s - a) t) = true := by
        rw [hsb]
        simp only [Bool.and_eq_true, Nat.blt_eq]
        exact ⟨⟨by omega, by omega⟩, hb⟩
      rw [if_pos hg, hsb]
      simp
    · by_cases hg : (Nat.blt a s && Nat.blt s (a + a) && memList (s - a) t) = true
      · rw [if_pos hg]
        exact List.mem_cons_of_mem _ (ihn hs')
      · rw [if_neg hg]
        exact ihn hs'

/-- Adding an entry to the list keeps the candidates already found. -/
private theorem mem_candidates_mono {x y : ℕ} {t : List ℕ} {c : List ℕ}
    (h : c ∈ candidates x t) : c ∈ candidates x (y :: t) := by
  rw [candidates_cons]
  by_cases hg : memList y (pairNeeds x) = true
  · rw [if_pos hg]
    exact List.mem_cons_of_mem _ (mem_candTrip_of_mem h _)
  · rw [if_neg hg]
    exact mem_candTrip_of_mem h _

/-- A power of three is generated as a one-element block. -/
private theorem mem_candidates_single {x : ℕ} (h : isPow3 x = true) (rest : List ℕ) :
    [x] ∈ candidates x rest := by
  induction rest with
  | nil =>
    rw [candidates_nil, if_pos h]
    simp
  | cons y t ih => exact mem_candidates_mono ih

/-- A partner of `x` on the list is generated as a two-element block. -/
private theorem mem_candidates_pair {x a : ℕ} {rest : List ℕ} (ha : a ∈ rest)
    (h : memList a (pairNeeds x) = true) : [x, a] ∈ candidates x rest := by
  obtain ⟨pre, t, rfl⟩ := List.append_of_mem ha
  clear ha
  induction pre with
  | nil =>
    rw [List.nil_append, candidates_cons, if_pos h]
    simp
  | cons p pre ih =>
    rw [List.cons_append]
    exact mem_candidates_mono ih

/-- Two entries of a decreasing list whose sum is admissible are generated as a three-element
block with `x`. -/
private theorem mem_candidates_triple {x a b : ℕ} {rest : List ℕ}
    (hsorted : rest.Pairwise (· > ·)) (ha : a ∈ rest) (hb : b ∈ rest) (hb0 : 0 < b) (hba : b < a)
    (hs : a + b ∈ tripNeeds x) : [x, a, b] ∈ candidates x rest := by
  obtain ⟨pre, t, rfl⟩ := List.append_of_mem ha
  have hbt : b ∈ t := by
    rcases List.mem_append.mp hb with hb' | hb'
    · exfalso
      have hgt : b > a := (List.pairwise_append.mp hsorted).2.2 b hb' a (by simp)
      omega
    · rcases List.mem_cons.mp hb' with rfl | hb'
      · exfalso; omega
      · exact hb'
  clear hb hsorted ha
  induction pre with
  | nil =>
    rw [List.nil_append, candidates_cons]
    have hmem : [x, a, b] ∈ candTrip x a t (candidates x t) (tripNeeds x) :=
      mem_candTrip hs hb0 hba (memList_eq_true.mpr hbt)
    by_cases hg : memList a (pairNeeds x) = true
    · rw [if_pos hg]
      exact List.mem_cons_of_mem _ hmem
    · rw [if_neg hg]
      exact hmem
  | cons p pre ih =>
    rw [List.cons_append]
    exact mem_candidates_mono ih

/-! ### The sets named by lists -/

/-- The empty list names the empty set. -/
private theorem toBlock_nil : toBlock [] = (∅ : Finset ℤ) := by
  simp [toBlock]

/-- Adding an entry to a list adds it to the set. -/
private theorem toBlock_cons (y : ℕ) (l : List ℕ) :
    toBlock (y :: l) = insert (y : ℤ) (toBlock l) := by
  simp [toBlock]

/-- The empty list of blocks names the empty partition. -/
private theorem toBlocks_nil : toBlocks [] = (∅ : Finset (Finset ℤ)) := by
  simp [toBlocks]

/-- Adding a block to a list adds it to the partition. -/
private theorem toBlocks_cons (b : List ℕ) (bs : List (List ℕ)) :
    toBlocks (b :: bs) = insert (toBlock b) (toBlocks bs) := by
  simp [toBlocks]

/-- The order of the blocks does not matter. -/
private theorem toBlocks_reverse (bs : List (List ℕ)) : toBlocks bs.reverse = toBlocks bs := by
  simp only [toBlocks, List.map_reverse, List.toFinset_reverse]

/-- Membership in the list with the entries of `B` removed. -/
private theorem mem_removeAll {y : ℕ} {B t : List ℕ} : y ∈ removeAll B t ↔ y ∈ t ∧ y ∉ B := by
  induction t with
  | nil => simp [removeAll_nil]
  | cons z s ih =>
    rw [removeAll_cons]
    by_cases hz : memList z B = true
    · rw [if_pos hz, ih]
      have hzB : z ∈ B := memList_eq_true.mp hz
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact absurd hzB h2
        · exact ⟨h1, h2⟩
    · rw [if_neg hz]
      have hzB : z ∉ B := fun h => hz (memList_eq_true.mpr h)
      simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hzB⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩

/-- Removing the entries of a block takes the difference of the sets. -/
private theorem toBlock_removeAll (B t : List ℕ) :
    toBlock (removeAll B t) = toBlock t \ toBlock B := by
  ext z
  simp only [Finset.mem_sdiff, mem_toBlock_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyt, hyB⟩ := mem_removeAll.mp hy
    refine ⟨⟨y, hyt, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwz⟩
    exact hyB ((Nat.cast_inj.mp hwz) ▸ hw)
  · rintro ⟨⟨y, hyt, rfl⟩, hnot⟩
    exact ⟨y, mem_removeAll.mpr ⟨hyt, fun h => hnot ⟨y, h, rfl⟩⟩, rfl⟩

/-- Removing entries does not lengthen the list. -/
private theorem removeAll_length_le (B t : List ℕ) : (removeAll B t).length ≤ t.length := by
  induction t with
  | nil => simp [removeAll_nil]
  | cons y s ih =>
    rw [removeAll_cons]
    by_cases hy : memList y B = true
    · rw [if_pos hy]
      simp only [List.length_cons]
      omega
    · rw [if_neg hy]
      simp only [List.length_cons]
      omega

/-- Removing entries keeps the list decreasing. -/
private theorem removeAll_pairwise {B t : List ℕ} (h : t.Pairwise (· > ·)) :
    (removeAll B t).Pairwise (· > ·) := by
  induction t with
  | nil =>
    rw [removeAll_nil]
    simp
  | cons y s ih =>
    obtain ⟨hy, hs⟩ := List.pairwise_cons.mp h
    rw [removeAll_cons]
    by_cases hm : memList y B = true
    · rw [if_pos hm]
      exact ih hs
    · rw [if_neg hm]
      exact List.pairwise_cons.mpr ⟨fun a ha => hy a (mem_removeAll.mp ha).1, ih hs⟩

/-- Membership in the descending list. -/
private theorem mem_downFrom {y n : ℕ} : y ∈ downFrom n ↔ 1 ≤ y ∧ y ≤ n := by
  induction n with
  | zero =>
    rw [downFrom_zero]
    simp
    omega
  | succ m ih =>
    rw [downFrom_succ]
    simp only [List.mem_cons, ih]
    omega

/-- The descending list is decreasing. -/
private theorem pairwise_downFrom (n : ℕ) : (downFrom n).Pairwise (· > ·) := by
  induction n with
  | zero =>
    rw [downFrom_zero]
    simp
  | succ m ih =>
    rw [downFrom_succ]
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro a ha
    have := (mem_downFrom.mp ha).2
    omega

/-- The descending list has one entry for each element to be covered. -/
private theorem length_downFrom (n : ℕ) : (downFrom n).length = n := by
  induction n with
  | zero => rw [downFrom_zero]; rfl
  | succ m ih => rw [downFrom_succ, List.length_cons, ih]

/-- The descending list names the interval. -/
private theorem toBlock_downFrom (n : ℕ) : toBlock (downFrom n) = interval n := by
  ext z
  simp only [mem_toBlock_iff, interval, Finset.mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := mem_downFrom.mp hy
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨z.toNat, mem_downFrom.mpr ⟨by omega, by omega⟩, by omega⟩

/-- A universal test over a list of blocks holds of each of them. -/
private theorem allB_mem {f : List ℕ → Bool} {l : List (List ℕ)} (h : allB f l = true)
    {b : List ℕ} (hb : b ∈ l) : f b = true := by
  induction l with
  | nil => simp at hb
  | cons c cs ihn =>
    rw [allB_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact h1
    · exact ihn h2 hb'

/-- The only good partition of the empty set is the empty one. -/
private theorem goodOn_empty_eq {bs : Finset (Finset ℤ)} (h : GoodOn ∅ bs) : bs = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro b hb
  obtain ⟨y, hy⟩ := (h.block hb).1
  have hmem := h.subset hb hy
  simp at hmem

/-! ### Completeness of the search -/

/-- Candidate completeness: a good block of the interval that contains the largest remaining element
is one of the generated candidates. -/
theorem mem_candidates_of {x : ℕ} {rest : List ℕ} (hsorted : rest.Pairwise (· > ·))
    (hlt : ∀ a ∈ rest, a < x) (hpos : ∀ a ∈ rest, 0 < a) (hbd : 3 * x < 729) {B : Finset ℤ}
    (hx : (x : ℤ) ∈ B) (hsub : B ⊆ toBlock (x :: rest)) (hcard : B.card ≤ 3)
    (hsum : ∃ k : ℕ, B.sum id = (3 : ℤ) ^ k) :
    ∃ b ∈ candidates x rest, toBlock b = B := by
  obtain ⟨k, hk⟩ := hsum
  -- every entry of the block other than `x` is an entry of the list
  have hrest : ∀ z ∈ B, z ≠ (x : ℤ) → ∃ a, a ∈ rest ∧ (a : ℤ) = z := by
    intro z hz hne
    obtain ⟨y, hy, rfl⟩ := mem_toBlock_iff.mp (hsub hz)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact absurd rfl hne
    · exact ⟨y, hy, rfl⟩
  -- the three-element case, with the two smaller entries named in decreasing order
  have key3 : ∀ a b : ℕ, a ∈ rest → b ∈ rest → b < a → (x : ℤ) + a + b = (3 : ℤ) ^ k →
      ∃ c ∈ candidates x rest, toBlock c = insert (x : ℤ) (insert (a : ℤ) {(b : ℤ)}) := by
    intro a b ha hb hba hsum3
    have hax : a < x := hlt a ha
    have hb0 : 0 < b := hpos b hb
    have hsn : x + a + b = 3 ^ k := by
      have hcast : ((x + a + b : ℕ) : ℤ) = ((3 ^ k : ℕ) : ℤ) := by push_cast; linarith
      exact Nat.cast_inj.mp hcast
    have hs2 : a + b ∈ tripNeeds x := by
      rw [tripNeeds_eq]
      have h3 : 3 ^ k - x = a + b := by omega
      exact h3 ▸ mem_tripLoop (pow3_mem_pow3s (by omega)) (by omega) (by omega)
    refine ⟨[x, a, b], mem_candidates_triple hsorted ha hb hb0 hba hs2, ?_⟩
    simp [toBlock]
  -- the block is `x` together with at most two entries of the list
  have hBins : insert (x : ℤ) (B.erase (x : ℤ)) = B := Finset.insert_erase hx
  have hxC : (x : ℤ) ∉ B.erase (x : ℤ) := Finset.notMem_erase _ _
  have hCcard : (B.erase (x : ℤ)).card ≤ 2 := by
    have h1 : (B.erase (x : ℤ)).card = B.card - 1 := Finset.card_erase_of_mem hx
    have h2 : 1 ≤ B.card := Finset.card_pos.mpr ⟨_, hx⟩
    omega
  have hcases : (B.erase (x : ℤ)).card = 0 ∨ (B.erase (x : ℤ)).card = 1 ∨
      (B.erase (x : ℤ)).card = 2 := by omega
  rcases hcases with hc | hc | hc
  · -- the one-element block `{x}`
    have hB : B = {(x : ℤ)} := by
      rw [← hBins, Finset.card_eq_zero.mp hc]
      simp
    have hs1 : (x : ℤ) = (3 : ℤ) ^ k := by
      rw [hB, Finset.sum_singleton] at hk
      simpa using hk
    have hsn : x = 3 ^ k := by
      have hcast : ((x : ℕ) : ℤ) = ((3 ^ k : ℕ) : ℤ) := by push_cast; linarith
      exact Nat.cast_inj.mp hcast
    refine ⟨[x], mem_candidates_single ?_ rest, ?_⟩
    · rw [hsn]
      exact isPow3_pow (by omega)
    · rw [hB]
      simp [toBlock]
  · -- the two-element block `{x, a}`
    obtain ⟨u, hCu⟩ := Finset.card_eq_one.mp hc
    have huB : u ∈ B := by
      rw [← hBins, hCu]
      simp
    have hxu : (x : ℤ) ≠ u := by
      rintro rfl
      rw [hCu] at hxC
      simp at hxC
    obtain ⟨a, ha, rfl⟩ := hrest u huB (Ne.symm hxu)
    have hax : a < x := hlt a ha
    have ha0 : 0 < a := hpos a ha
    have hB : B = insert (x : ℤ) {(a : ℤ)} := by rw [← hBins, hCu]
    have hs2 : (x : ℤ) + (a : ℤ) = (3 : ℤ) ^ k := by
      rw [hB, Finset.sum_insert (by simpa using hxu), Finset.sum_singleton] at hk
      simpa using hk
    have hsn : x + a = 3 ^ k := by
      have hcast : ((x + a : ℕ) : ℤ) = ((3 ^ k : ℕ) : ℤ) := by push_cast; linarith
      exact Nat.cast_inj.mp hcast
    have hmem : a ∈ pairNeeds x := by
      rw [pairNeeds_eq]
      have h3 : 3 ^ k - x = a := by omega
      exact h3 ▸ mem_pairLoop (pow3_mem_pow3s (by omega)) (by omega) (by omega)
    refine ⟨[x, a], mem_candidates_pair ha (memList_eq_true.mpr hmem), ?_⟩
    rw [hB]
    simp [toBlock]
  · -- the three-element block `{x, a, b}`
    obtain ⟨u, v, huv, hCuv⟩ := Finset.card_eq_two.mp hc
    have huB : u ∈ B := by
      rw [← hBins, hCuv]
      simp
    have hvB : v ∈ B := by
      rw [← hBins, hCuv]
      simp
    have hxu : (x : ℤ) ≠ u := by
      rintro rfl
      rw [hCuv] at hxC
      simp at hxC
    have hxv : (x : ℤ) ≠ v := by
      rintro rfl
      rw [hCuv] at hxC
      simp at hxC
    obtain ⟨a, ha, rfl⟩ := hrest u huB (Ne.symm hxu)
    obtain ⟨b, hb, rfl⟩ := hrest v hvB (Ne.symm hxv)
    have hB : B = insert (x : ℤ) (insert (a : ℤ) {(b : ℤ)}) := by rw [← hBins, hCuv]
    have hs3 : (x : ℤ) + (a : ℤ) + (b : ℤ) = (3 : ℤ) ^ k := by
      rw [hB, Finset.sum_insert (by simp [hxu, hxv]), Finset.sum_insert (by simpa using huv),
        Finset.sum_singleton] at hk
      simp only [id_eq] at hk
      linarith
    have hab : a ≠ b := fun h => huv (by rw [h])
    rcases Nat.lt_or_ge a b with hlt' | hge
    · obtain ⟨c, hc1, hc2⟩ := key3 b a hb ha hlt' (by linarith)
      refine ⟨c, hc1, ?_⟩
      rw [hc2, hB, Finset.pair_comm]
    · have hba : b < a := by omega
      obtain ⟨c, hc1, hc2⟩ := key3 a b ha hb hba (by linarith)
      exact ⟨c, hc1, by rw [hc2, hB]⟩

/-- The search accepts only the listed partitions, however many blocks have been chosen: if it
accepts from a list of remaining elements with a prefix of blocks already chosen, then every good
partition of the set named by the list, together with those blocks, is one of the listed
partitions. -/
private theorem searchAll_complete_aux (expected : List (List (List ℕ))) :
    ∀ (fuel : ℕ) (rest : List ℕ) (acc : List (List ℕ)), rest.Pairwise (· > ·) →
      (∀ y ∈ rest, 0 < y) → (∀ y ∈ rest, 3 * y < 729) → rest.length ≤ fuel →
      searchAll expected fuel rest acc = true →
      ∀ bs : Finset (Finset ℤ), GoodOn (toBlock rest) bs →
        ∃ w ∈ expected, toBlocks acc ∪ bs = toBlocks w := by
  have hnil : ∀ (acc : List (List ℕ)), expected.contains acc.reverse = true →
      ∀ bs : Finset (Finset ℤ), GoodOn (toBlock []) bs →
        ∃ w ∈ expected, toBlocks acc ∪ bs = toBlocks w := by
    intro acc h bs hbs
    refine ⟨acc.reverse, List.contains_iff_mem.mp h, ?_⟩
    rw [toBlock_nil] at hbs
    rw [goodOn_empty_eq hbs, toBlocks_reverse, Finset.union_empty]
  intro fuel
  induction fuel with
  | zero =>
    intro rest acc _ _ _ hfuel h
    cases rest with
    | nil =>
      rw [searchAll_zero_nil] at h
      exact hnil acc h
    | cons x t => simp at hfuel
  | succ f ih =>
    intro rest acc hsorted hpos hbd hfuel h
    cases rest with
    | nil =>
      rw [searchAll_succ_nil] at h
      exact hnil acc h
    | cons x t =>
      rw [searchAll_succ_cons] at h
      intro bs hbs
      -- the block of the largest element
      have hxu : (x : ℤ) ∈ bs.biUnion id := by
        rw [hbs.1, toBlock_cons]
        exact Finset.mem_insert_self _ _
      obtain ⟨B₀, hB₀, hxB₀⟩ := Finset.mem_biUnion.mp hxu
      obtain ⟨-, hcard, hsum⟩ := hbs.block hB₀
      obtain ⟨b, hbc, hbeq⟩ :=
        mem_candidates_of (List.pairwise_cons.mp hsorted).2
          (List.pairwise_cons.mp hsorted).1 (fun a ha => hpos a (List.mem_cons_of_mem _ ha))
          (hbd x (by simp)) hxB₀ (hbs.subset hB₀) hcard hsum
      -- the search accepted the branch through that block
      have hrec : searchAll expected f (removeAll b t) (b :: acc) = true := allB_mem h hbc
      -- what is left to cover after the block is removed
      have hset : toBlock (removeAll b t) = toBlock (x :: t) \ B₀ := by
        rw [toBlock_removeAll, hbeq, toBlock_cons]
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hz, hz2⟩
          exact ⟨Or.inr hz, hz2⟩
        · rintro ⟨rfl | hz, hz2⟩
          · exact absurd hxB₀ hz2
          · exact ⟨hz, hz2⟩
      have hgood : GoodOn (toBlock (removeAll b t)) (bs.erase B₀) := by
        rw [hset]
        exact hbs.erase hB₀
      have hlen : (removeAll b t).length ≤ f := by
        have h1 := removeAll_length_le b t
        simp only [List.length_cons] at hfuel
        omega
      obtain ⟨w, hw, hweq⟩ := ih (removeAll b t) (b :: acc)
        (removeAll_pairwise (List.pairwise_cons.mp hsorted).2)
        (fun y hy => hpos y (List.mem_cons_of_mem _ (mem_removeAll.mp hy).1))
        (fun y hy => hbd y (List.mem_cons_of_mem _ (mem_removeAll.mp hy).1))
        hlen hrec _ hgood
      refine ⟨w, hw, ?_⟩
      rw [← hweq, toBlocks_cons, hbeq]
      ext S
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (hS | hS)
        · exact Or.inl (Or.inr hS)
        · by_cases hSB : S = B₀
          · exact Or.inl (Or.inl hSB)
          · exact Or.inr ⟨hSB, hS⟩
      · rintro ((rfl | hS) | ⟨-, hS⟩)
        · exact Or.inr hB₀
        · exact Or.inl hS
        · exact Or.inr hS

/-- The search invariant: if the search from `rest` with the blocks of `acc` already chosen accepts,
then every good partition of the set of `rest`, together with those blocks, is one of the expected
partitions. -/
theorem searchAll_complete (fuel : ℕ) (rest : List ℕ) (acc : List (List ℕ))
    (expected : List (List (List ℕ))) (hsorted : rest.Pairwise (· > ·)) (hpos : ∀ y ∈ rest, 0 < y)
    (hbd : ∀ y ∈ rest, 3 * y < 729) (hfuel : rest.length ≤ fuel)
    (h : searchAll expected fuel rest acc = true) :
    ∀ bs : Finset (Finset ℤ), GoodOn (toBlock rest) bs →
      ∃ w ∈ expected, toBlocks acc ∪ bs = toBlocks w :=
  searchAll_complete_aux expected fuel rest acc hsorted hpos hbd hfuel h

/-- An accepting search lists every good partition of `{1, …, n}`. -/
theorem complete_of_search {n : ℕ} {expected : List (List (List ℕ))} (hn : 3 * n < 729)
    (h : search n expected = true) :
    ∀ bs, IsGoodPartition n bs → ∃ w ∈ expected, bs = toBlocks w := by
  intro bs hbs
  have h' : searchAll expected n (downFrom n) [] = true := h
  have hgood : GoodOn (toBlock (downFrom n)) bs := by
    rw [toBlock_downFrom]
    exact (isGoodPartition_iff n bs).mp hbs
  obtain ⟨w, hw, hweq⟩ := searchAll_complete n (downFrom n) [] expected (pairwise_downFrom n)
    (fun y hy => (mem_downFrom.mp hy).1)
    (fun y hy => by have := (mem_downFrom.mp hy).2; omega)
    (by rw [length_downFrom]) h' bs hgood
  refine ⟨w, hw, ?_⟩
  rw [← hweq, toBlocks_nil, Finset.empty_union]

/-- One checked witness and an accepting search against it give a count of one. -/
theorem count_eq_one_of_search {n : ℕ} {w : List (List ℕ)} (hn : 3 * n < 729)
    (hw : checkPartition n w = true) (h : search n [w] = true) : count n = 1 := by
  refine count_eq_one_of (isGoodPartition_of_checkPartition hw) ?_
  intro bs hbs
  obtain ⟨w', hw', hbs'⟩ := complete_of_search hn h bs hbs
  rw [List.mem_singleton] at hw'
  rw [hbs', hw']

/-- Two checked, differing witnesses and an accepting search against them give a count of two. -/
theorem count_eq_two_of_search {n : ℕ} {w₁ w₂ : List (List ℕ)} (hn : 3 * n < 729)
    (h₁ : checkPartition n w₁ = true) (h₂ : checkPartition n w₂ = true)
    (hd : differ w₁ w₂ = true) (h : search n [w₁, w₂] = true) : count n = 2 := by
  refine count_eq_two_of (isGoodPartition_of_checkPartition h₁)
    (isGoodPartition_of_checkPartition h₂) (toBlocks_ne_of_differ h₁ h₂ hd) ?_
  intro bs hbs
  obtain ⟨w', hw', hbs'⟩ := complete_of_search hn h bs hbs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with rfl | rfl
  · exact Or.inl hbs'
  · exact Or.inr hbs'

end GNM

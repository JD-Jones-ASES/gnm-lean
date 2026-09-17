import GN.Langford

namespace GN
noncomputable section

set_option maxHeartbeats 0
/-! Explicit ordinary extended Langford tables from Mor--Linek (2014),
DOI 10.2478/s12175-014-0242-6, Tables 2,3,6,7,10,11. Each theorem below
proves the formula by integer arithmetic; no sequence existence axiom is used.
The printed headings for Tables7b/7c have order2d+5, but their formulas
and the surrounding Lemma6.2 give order2d+6, as verified here. -/

/-- Table2a, defect `2*q`, last difference `6*q+4`. -/
def langfordRows2a (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(1,3*q+5)} ∪
  {(3,3*q+6)} ∪
  affinePairs (4) (4*q+9) (2*q-1) ∪
  hingedPairs (2*q+4) (2) (q) h ∪
  hingedPairs (3*q+7) (2) (q-2) h ∪
  {(4*q+7,8*q+11)} ∪
  {(6*q+8,8*q+9)} ∪
  {(6*q+10,8*q+10)}

def langfordHole2a (q h : ℤ) : Prop :=
  h=2 ∨
  (4*q+6 ≤ h ∧ h ≤ 6*q+6 ∧ (h-(4*q+6))%2=0) ∨
  (6*q+12 ≤ h ∧ h ≤ 8*q+8 ∧ (h-(6*q+12))%2=0)

theorem langfordRows2a_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole2a q h) :
    pairEndpoints (langfordRows2a q h) = (Finset.Icc 1 (8*q+11)).erase h := by
  unfold langfordHole2a at hh
  ext x
  simp only [langfordRows2a, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=2
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows2a_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows2a q h) = Finset.Icc (2*q) (6*q+4) := by
  ext x
  simp only [langfordRows2a, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows2a_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows2a q h).card ≤ (4*q+5).toNat := by
  have hc : (langfordRows2a q h).card ≤ 1+1+(2*q-1+1).toNat+(q+1).toNat+(q-2+1).toNat+1+1+1 := by
    unfold langfordRows2a
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows2a_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole2a q h) :
    LangfordPairing (2*q) (6*q+4) h (langfordRows2a q h) := by
  have hh' := hh
  unfold langfordHole2a at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows2a_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows2a_differences q h hq
  · convert langfordRows2a_card q h hq using 1 <;> congr 1 <;> omega

/-- Table2b, defect `2*q`, last difference `6*q+4`. -/
def langfordRows2b (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(1,2*q+4)} ∪
  {(3,2*q+7)} ∪
  affinePairs (4) (4*q+9) (q-2) ∪
  {(q+3,4*q+8)} ∪
  affinePairs (q+4) (6*q+9) (q-1) ∪
  {(2*q+5,4*q+10)} ∪
  {(2*q+6,4*q+7)} ∪
  hingedPairs (2*q+8) (2) (q-2) h ∪
  {(3*q+7,8*q+11)} ∪
  hingedPairs (3*q+8) (2) (q-2) h ∪
  {(4*q+12,6*q+12)} ∪
  {(6*q+7,8*q+9)}

def langfordHole2b (q h : ℤ) : Prop :=
  h=2 ∨
  (4*q+14 ≤ h ∧ h ≤ 6*q+10 ∧ (h-(4*q+14))%2=0) ∨
  (6*q+14 ≤ h ∧ h ≤ 8*q+10 ∧ (h-(6*q+14))%2=0)

theorem langfordRows2b_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole2b q h) :
    pairEndpoints (langfordRows2b q h) = (Finset.Icc 1 (8*q+11)).erase h := by
  unfold langfordHole2b at hh
  ext x
  simp only [langfordRows2b, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=2
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows2b_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows2b q h) = Finset.Icc (2*q) (6*q+4) := by
  ext x
  simp only [langfordRows2b, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows2b_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows2b q h).card ≤ (4*q+5).toNat := by
  have hc : (langfordRows2b q h).card ≤ 1+1+(q-2+1).toNat+1+(q-1+1).toNat+1+1+(q-2+1).toNat+1+(q-2+1).toNat+1+1 := by
    unfold langfordRows2b
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows2b_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole2b q h) :
    LangfordPairing (2*q) (6*q+4) h (langfordRows2b q h) := by
  have hh' := hh
  unfold langfordHole2b at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows2b_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows2b_differences q h hq
  · convert langfordRows2b_card q h hq using 1 <;> congr 1 <;> omega

/-- Table3a, defect `2*q+1`, last difference `6*q+7`. -/
def langfordRows3a (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(1,3*q+6)} ∪
  {(2,2*q+4)} ∪
  {(3,3*q+7)} ∪
  affinePairs (4) (4*q+11) (2*q-1) ∪
  {(2*q+5,8*q+12)} ∪
  affinePairs (2*q+6) (4*q+10) (q-1) ∪
  affinePairs (3*q+8) (6*q+14) (q-2) ∪
  {(4*q+7,8*q+13)} ∪
  {(4*q+9,8*q+14)} ∪
  {(6*q+10,8*q+11)} ∪
  {(6*q+12,8*q+15)}

def langfordHole3a (q h : ℤ) : Prop :=
  h=4*q+8

theorem langfordRows3a_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole3a q h) :
    pairEndpoints (langfordRows3a q h) = (Finset.Icc 1 (8*q+15)).erase h := by
  unfold langfordHole3a at hh
  ext x
  simp only [langfordRows3a, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 <;> omega
  · by_cases hxz : x=4*q+8
    · subst x
      rcases hh with hh0 <;> omega
    ·
      clear hh
      omega

theorem langfordRows3a_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows3a q h) = Finset.Icc (2*q+1) (6*q+7) := by
  ext x
  simp only [langfordRows3a, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows3a_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows3a q h).card ≤ (4*q+7).toNat := by
  have hc : (langfordRows3a q h).card ≤ 1+1+1+(2*q-1+1).toNat+1+(q-1+1).toNat+(q-2+1).toNat+1+1+1+1 := by
    unfold langfordRows3a
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows3a_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole3a q h) :
    LangfordPairing (2*q+1) (6*q+7) h (langfordRows3a q h) := by
  have hh' := hh
  unfold langfordHole3a at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows3a_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows3a_differences q h hq
  · convert langfordRows3a_card q h hq using 1 <;> congr 1 <;> omega

/-- Table3b, defect `2*q+1`, last difference `6*q+7`. -/
def langfordRows3b (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(1,4*q+6)} ∪
  {(3,2*q+5)} ∪
  affinePairs (4) (4*q+11) (q-2) ∪
  {(q+3,4*q+7)} ∪
  {(q+4,6*q+10)} ∪
  affinePairs (q+5) (6*q+13) (q-1) ∪
  hingedPairs (2*q+6) (2) (q-1) h ∪
  {(3*q+6,8*q+13)} ∪
  hingedPairs (3*q+7) (2) (q-2) h ∪
  {(4*q+8,8*q+12)} ∪
  {(4*q+9,8*q+15)} ∪
  {(6*q+9,8*q+10)} ∪
  {(6*q+11,8*q+14)}

def langfordHole3b (q h : ℤ) : Prop :=
  h=2 ∨
  (4*q+10 ≤ h ∧ h ≤ 6*q+8 ∧ (h-(4*q+10))%2=0) ∨
  (6*q+12 ≤ h ∧ h ≤ 8*q+8 ∧ (h-(6*q+12))%2=0)

theorem langfordRows3b_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole3b q h) :
    pairEndpoints (langfordRows3b q h) = (Finset.Icc 1 (8*q+15)).erase h := by
  unfold langfordHole3b at hh
  ext x
  simp only [langfordRows3b, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=2
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows3b_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows3b q h) = Finset.Icc (2*q+1) (6*q+7) := by
  ext x
  simp only [langfordRows3b, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows3b_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows3b q h).card ≤ (4*q+7).toNat := by
  have hc : (langfordRows3b q h).card ≤ 1+1+(q-2+1).toNat+1+1+(q-1+1).toNat+(q-1+1).toNat+1+(q-2+1).toNat+1+1+1+1 := by
    unfold langfordRows3b
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows3b_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole3b q h) :
    LangfordPairing (2*q+1) (6*q+7) h (langfordRows3b q h) := by
  have hh' := hh
  unfold langfordHole3b at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows3b_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows3b_differences q h hq
  · convert langfordRows3b_card q h hq using 1 <;> congr 1 <;> omega

/-- Table3c, defect `2*q+1`, last difference `6*q+7`. -/
def langfordRows3c (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(1,3*q+7)} ∪
  {(3,2*q+7)} ∪
  affinePairs (4) (4*q+11) (q) ∪
  {(q+5,4*q+10)} ∪
  {(q+6,3*q+8)} ∪
  affinePairs (q+7) (6*q+15) (q-1) ∪
  hingedPairs (2*q+8) (2) (q-2) h ∪
  hingedPairs (3*q+9) (2) (q-1) h ∪
  {(4*q+9,6*q+14)} ∪
  {(4*q+12,6*q+13)} ∪
  {(6*q+12,8*q+15)}

def langfordHole3c (q h : ℤ) : Prop :=
  h=2 ∨
  (4*q+14 ≤ h ∧ h ≤ 6*q+10 ∧ (h-(4*q+14))%2=0) ∨
  (6*q+16 ≤ h ∧ h ≤ 8*q+14 ∧ (h-(6*q+16))%2=0)

theorem langfordRows3c_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole3c q h) :
    pairEndpoints (langfordRows3c q h) = (Finset.Icc 1 (8*q+15)).erase h := by
  unfold langfordHole3c at hh
  ext x
  simp only [langfordRows3c, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=2
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows3c_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows3c q h) = Finset.Icc (2*q+1) (6*q+7) := by
  ext x
  simp only [langfordRows3c, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows3c_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows3c q h).card ≤ (4*q+7).toNat := by
  have hc : (langfordRows3c q h).card ≤ 1+1+(q+1).toNat+1+1+(q-1+1).toNat+(q-2+1).toNat+(q-1+1).toNat+1+1+1 := by
    unfold langfordRows3c
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows3c_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole3c q h) :
    LangfordPairing (2*q+1) (6*q+7) h (langfordRows3c q h) := by
  have hh' := hh
  unfold langfordHole3c at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows3c_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows3c_differences q h hq
  · convert langfordRows3c_card q h hq using 1 <;> congr 1 <;> omega

/-- Table6a, defect `2*q`, last difference `6*q+5`. -/
def langfordRows6a (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(1,2*q+3)} ∪
  {(3,3*q+6)} ∪
  affinePairs (4) (4*q+11) (q-2) ∪
  {(q+3,4*q+7)} ∪
  affinePairs (q+4) (6*q+11) (q-2) ∪
  {(2*q+4,6*q+9)} ∪
  hingedPairs (2*q+5) (2) (q-1) h ∪
  {(3*q+5,8*q+11)} ∪
  hingedPairs (3*q+7) (2) (q-2) h ∪
  {(4*q+6,8*q+12)} ∪
  {(4*q+9,8*q+13)} ∪
  {(6*q+8,8*q+9)} ∪
  {(6*q+10,8*q+10)}

def langfordHole6a (q h : ℤ) : Prop :=
  h=2 ∨
  (4*q+8 ≤ h ∧ h ≤ 6*q+6 ∧ (h-(4*q+8))%2=0) ∨
  (6*q+12 ≤ h ∧ h ≤ 8*q+8 ∧ (h-(6*q+12))%2=0)

theorem langfordRows6a_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole6a q h) :
    pairEndpoints (langfordRows6a q h) = (Finset.Icc 1 (8*q+13)).erase h := by
  unfold langfordHole6a at hh
  ext x
  simp only [langfordRows6a, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=2
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows6a_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows6a q h) = Finset.Icc (2*q) (6*q+5) := by
  ext x
  simp only [langfordRows6a, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows6a_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows6a q h).card ≤ (4*q+6).toNat := by
  have hc : (langfordRows6a q h).card ≤ 1+1+(q-2+1).toNat+1+(q-2+1).toNat+1+(q-1+1).toNat+1+(q-2+1).toNat+1+1+1+1 := by
    unfold langfordRows6a
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows6a_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole6a q h) :
    LangfordPairing (2*q) (6*q+5) h (langfordRows6a q h) := by
  have hh' := hh
  unfold langfordHole6a at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows6a_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows6a_differences q h hq
  · convert langfordRows6a_card q h hq using 1 <;> congr 1 <;> omega

/-- Table6b, defect `2*q`, last difference `6*q+5`. -/
def langfordRows6b (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(1,2*q+5)} ∪
  affinePairs (3) (4*q+9) (q) ∪
  {(q+4,3*q+7)} ∪
  {(q+5,4*q+10)} ∪
  affinePairs (q+6) (6*q+13) (q-2) ∪
  {(2*q+6,4*q+8)} ∪
  hingedPairs (2*q+7) (2) (q-1) h ∪
  hingedPairs (3*q+8) (2) (q-1) h ∪
  {(6*q+11,8*q+11)} ∪
  {(6*q+12,8*q+13)}

def langfordHole6b (q h : ℤ) : Prop :=
  h=2 ∨
  (4*q+12 ≤ h ∧ h ≤ 6*q+10 ∧ (h-(4*q+12))%2=0) ∨
  (6*q+14 ≤ h ∧ h ≤ 8*q+12 ∧ (h-(6*q+14))%2=0)

theorem langfordRows6b_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole6b q h) :
    pairEndpoints (langfordRows6b q h) = (Finset.Icc 1 (8*q+13)).erase h := by
  unfold langfordHole6b at hh
  ext x
  simp only [langfordRows6b, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=2
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows6b_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows6b q h) = Finset.Icc (2*q) (6*q+5) := by
  ext x
  simp only [langfordRows6b, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows6b_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows6b q h).card ≤ (4*q+6).toNat := by
  have hc : (langfordRows6b q h).card ≤ 1+(q+1).toNat+1+1+(q-2+1).toNat+1+(q-1+1).toNat+(q-1+1).toNat+1+1 := by
    unfold langfordRows6b
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows6b_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole6b q h) :
    LangfordPairing (2*q) (6*q+5) h (langfordRows6b q h) := by
  have hh' := hh
  unfold langfordHole6b at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows6b_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows6b_differences q h hq
  · convert langfordRows6b_card q h hq using 1 <;> congr 1 <;> omega

/-- Table7a, defect `2*q+1`, last difference `6*q+8`. -/
def langfordRows7a (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(1,2*q+5)} ∪
  {(2,2*q+4)} ∪
  affinePairs (3) (4*q+11) (q-1) ∪
  {(q+3,3*q+6)} ∪
  affinePairs (q+4) (6*q+13) (q-1) ∪
  affinePairs (2*q+6) (4*q+12) (q-1) ∪
  {(3*q+7,8*q+15)} ∪
  affinePairs (3*q+8) (6*q+14) (q) ∪
  {(4*q+10,8*q+17)} ∪
  {(6*q+11,8*q+16)} ∪
  {(6*q+12,8*q+13)}

def langfordHole7a (q h : ℤ) : Prop :=
  h=4*q+9

theorem langfordRows7a_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole7a q h) :
    pairEndpoints (langfordRows7a q h) = (Finset.Icc 1 (8*q+17)).erase h := by
  unfold langfordHole7a at hh
  ext x
  simp only [langfordRows7a, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 <;> omega
  · by_cases hxz : x=4*q+9
    · subst x
      rcases hh with hh0 <;> omega
    ·
      clear hh
      omega

theorem langfordRows7a_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows7a q h) = Finset.Icc (2*q+1) (6*q+8) := by
  ext x
  simp only [langfordRows7a, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows7a_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows7a q h).card ≤ (4*q+8).toNat := by
  have hc : (langfordRows7a q h).card ≤ 1+1+(q-1+1).toNat+1+(q-1+1).toNat+(q-1+1).toNat+1+(q+1).toNat+1+1+1 := by
    unfold langfordRows7a
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows7a_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole7a q h) :
    LangfordPairing (2*q+1) (6*q+8) h (langfordRows7a q h) := by
  have hh' := hh
  unfold langfordHole7a at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows7a_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows7a_differences q h hq
  · convert langfordRows7a_card q h hq using 1 <;> congr 1 <;> omega

/-- Table7b, defect `2*q+1`, last difference `6*q+8`. -/
def langfordRows7b (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(2,2*q+5)} ∪
  affinePairs (3) (4*q+12) (q-1) ∪
  {(q+3,4*q+10)} ∪
  {(q+4,3*q+8)} ∪
  affinePairs (q+5) (6*q+14) (q-1) ∪
  hingedPairs (2*q+6) (1) (q+1) h ∪
  hingedPairs (3*q+9) (1) (q) h ∪
  {(6*q+12,8*q+14)} ∪
  {(6*q+15,8*q+16)}

def langfordHole7b (q h : ℤ) : Prop :=
  h=1 ∨
  (4*q+11 ≤ h ∧ h ≤ 6*q+13 ∧ (h-(4*q+11))%2=0) ∨
  (6*q+17 ≤ h ∧ h ≤ 8*q+17 ∧ (h-(6*q+17))%2=0)

theorem langfordRows7b_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole7b q h) :
    pairEndpoints (langfordRows7b q h) = (Finset.Icc 1 (8*q+17)).erase h := by
  unfold langfordHole7b at hh
  ext x
  simp only [langfordRows7b, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=1
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows7b_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows7b q h) = Finset.Icc (2*q+1) (6*q+8) := by
  ext x
  simp only [langfordRows7b, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows7b_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows7b q h).card ≤ (4*q+8).toNat := by
  have hc : (langfordRows7b q h).card ≤ 1+(q-1+1).toNat+1+1+(q-1+1).toNat+(q+1+1).toNat+(q+1).toNat+1+1 := by
    unfold langfordRows7b
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows7b_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole7b q h) :
    LangfordPairing (2*q+1) (6*q+8) h (langfordRows7b q h) := by
  have hh' := hh
  unfold langfordHole7b at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows7b_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows7b_differences q h hq
  · convert langfordRows7b_card q h hq using 1 <;> congr 1 <;> omega

/-- Table7c, defect `2*q+1`, last difference `6*q+8`. -/
def langfordRows7c (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(2,2*q+5)} ∪
  affinePairs (3) (4*q+12) (q-1) ∪
  {(q+3,4*q+9)} ∪
  {(q+4,3*q+6)} ∪
  affinePairs (q+5) (6*q+14) (q-1) ∪
  hingedPairs (2*q+6) (1) (q-1) h ∪
  {(3*q+7,6*q+12)} ∪
  hingedPairs (3*q+8) (1) (q-1) h ∪
  {(4*q+8,8*q+16)} ∪
  {(4*q+10,8*q+17)} ∪
  {(6*q+11,8*q+15)} ∪
  {(6*q+13,8*q+14)}

def langfordHole7c (q h : ℤ) : Prop :=
  h=1 ∨
  (4*q+11 ≤ h ∧ h ≤ 6*q+9 ∧ (h-(4*q+11))%2=0) ∨
  (6*q+15 ≤ h ∧ h ≤ 8*q+13 ∧ (h-(6*q+15))%2=0)

theorem langfordRows7c_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole7c q h) :
    pairEndpoints (langfordRows7c q h) = (Finset.Icc 1 (8*q+17)).erase h := by
  unfold langfordHole7c at hh
  ext x
  simp only [langfordRows7c, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=1
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows7c_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows7c q h) = Finset.Icc (2*q+1) (6*q+8) := by
  ext x
  simp only [langfordRows7c, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows7c_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows7c q h).card ≤ (4*q+8).toNat := by
  have hc : (langfordRows7c q h).card ≤ 1+(q-1+1).toNat+1+1+(q-1+1).toNat+(q-1+1).toNat+1+(q-1+1).toNat+1+1+1+1 := by
    unfold langfordRows7c
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows7c_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole7c q h) :
    LangfordPairing (2*q+1) (6*q+8) h (langfordRows7c q h) := by
  have hh' := hh
  unfold langfordHole7c at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows7c_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows7c_differences q h hq
  · convert langfordRows7c_card q h hq using 1 <;> congr 1 <;> omega

/-- Table10a, defect `2*q`, last difference `6*q+6`. -/
def langfordRows10a (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(2,3*q+7)} ∪
  {(3,2*q+5)} ∪
  affinePairs (4) (4*q+12) (q-1) ∪
  {(q+4,4*q+10)} ∪
  {(q+5,3*q+6)} ∪
  affinePairs (q+6) (6*q+14) (q-2) ∪
  hingedPairs (2*q+6) (1) (q-1) h ∪
  hingedPairs (3*q+8) (1) (q) h ∪
  {(4*q+9,6*q+13)} ∪
  {(6*q+11,8*q+14)} ∪
  {(6*q+12,8*q+12)}

def langfordHole10a (q h : ℤ) : Prop :=
  h=1 ∨
  (4*q+11 ≤ h ∧ h ≤ 6*q+9 ∧ (h-(4*q+11))%2=0) ∨
  (6*q+15 ≤ h ∧ h ≤ 8*q+15 ∧ (h-(6*q+15))%2=0)

theorem langfordRows10a_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole10a q h) :
    pairEndpoints (langfordRows10a q h) = (Finset.Icc 1 (8*q+15)).erase h := by
  unfold langfordHole10a at hh
  ext x
  simp only [langfordRows10a, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=1
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows10a_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows10a q h) = Finset.Icc (2*q) (6*q+6) := by
  ext x
  simp only [langfordRows10a, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows10a_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows10a q h).card ≤ (4*q+7).toNat := by
  have hc : (langfordRows10a q h).card ≤ 1+1+(q-1+1).toNat+1+1+(q-2+1).toNat+(q-1+1).toNat+(q+1).toNat+1+1+1 := by
    unfold langfordRows10a
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows10a_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole10a q h) :
    LangfordPairing (2*q) (6*q+6) h (langfordRows10a q h) := by
  have hh' := hh
  unfold langfordHole10a at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows10a_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows10a_differences q h hq
  · convert langfordRows10a_card q h hq using 1 <;> congr 1 <;> omega

/-- Table10b, defect `2*q`, last difference `6*q+6`. -/
def langfordRows10b (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(2,2*q+4)} ∪
  {(3,2*q+3)} ∪
  affinePairs (4) (4*q+12) (q-3) ∪
  {(q+2,4*q+6)} ∪
  affinePairs (q+3) (6*q+10) (q-1) ∪
  hingedPairs (2*q+5) (1) (q-1) h ∪
  {(3*q+5,8*q+11)} ∪
  hingedPairs (3*q+6) (1) (q-2) h ∪
  {(4*q+5,8*q+10)} ∪
  {(4*q+7,8*q+13)} ∪
  {(4*q+8,8*q+15)} ∪
  {(4*q+10,8*q+14)} ∪
  {(6*q+8,8*q+9)} ∪
  {(6*q+9,8*q+12)}

def langfordHole10b (q h : ℤ) : Prop :=
  h=1 ∨
  (4*q+9 ≤ h ∧ h ≤ 6*q+7 ∧ (h-(4*q+9))%2=0) ∨
  (6*q+11 ≤ h ∧ h ≤ 8*q+7 ∧ (h-(6*q+11))%2=0)

theorem langfordRows10b_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole10b q h) :
    pairEndpoints (langfordRows10b q h) = (Finset.Icc 1 (8*q+15)).erase h := by
  unfold langfordHole10b at hh
  ext x
  simp only [langfordRows10b, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=1
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows10b_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows10b q h) = Finset.Icc (2*q) (6*q+6) := by
  ext x
  simp only [langfordRows10b, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows10b_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows10b q h).card ≤ (4*q+7).toNat := by
  have hc : (langfordRows10b q h).card ≤ 1+1+(q-3+1).toNat+1+(q-1+1).toNat+(q-1+1).toNat+1+(q-2+1).toNat+1+1+1+1+1+1 := by
    unfold langfordRows10b
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows10b_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole10b q h) :
    LangfordPairing (2*q) (6*q+6) h (langfordRows10b q h) := by
  have hh' := hh
  unfold langfordHole10b at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows10b_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows10b_differences q h hq
  · convert langfordRows10b_card q h hq using 1 <;> congr 1 <;> omega

/-- Table11a, defect `2*q+1`, last difference `6*q+9`. -/
def langfordRows11a (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(2,4*q+11)} ∪
  {(3,3*q+9)} ∪
  affinePairs (4) (4*q+14) (q-1) ∪
  {(q+4,4*q+12)} ∪
  {(q+5,3*q+7)} ∪
  affinePairs (q+6) (6*q+16) (q-1) ∪
  {(2*q+6,4*q+10)} ∪
  hingedPairs (2*q+7) (1) (q-1) h ∪
  {(3*q+8,6*q+15)} ∪
  hingedPairs (3*q+10) (1) (q-1) h ∪
  {(6*q+13,8*q+16)} ∪
  {(6*q+14,8*q+19)} ∪
  {(6*q+17,8*q+18)}

def langfordHole11a (q h : ℤ) : Prop :=
  h=1 ∨
  (4*q+13 ≤ h ∧ h ≤ 6*q+11 ∧ (h-(4*q+13))%2=0) ∨
  (6*q+19 ≤ h ∧ h ≤ 8*q+17 ∧ (h-(6*q+19))%2=0)

theorem langfordRows11a_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole11a q h) :
    pairEndpoints (langfordRows11a q h) = (Finset.Icc 1 (8*q+19)).erase h := by
  unfold langfordHole11a at hh
  ext x
  simp only [langfordRows11a, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=1
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows11a_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows11a q h) = Finset.Icc (2*q+1) (6*q+9) := by
  ext x
  simp only [langfordRows11a, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows11a_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows11a q h).card ≤ (4*q+9).toNat := by
  have hc : (langfordRows11a q h).card ≤ 1+1+(q-1+1).toNat+1+1+(q-1+1).toNat+1+(q-1+1).toNat+1+(q-1+1).toNat+1+1+1 := by
    unfold langfordRows11a
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows11a_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole11a q h) :
    LangfordPairing (2*q+1) (6*q+9) h (langfordRows11a q h) := by
  have hh' := hh
  unfold langfordHole11a at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows11a_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows11a_differences q h hq
  · convert langfordRows11a_card q h hq using 1 <;> congr 1 <;> omega

/-- Table11b, defect `2*q+1`, last difference `6*q+9`. -/
def langfordRows11b (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(2,2*q+5)} ∪
  {(3,2*q+4)} ∪
  affinePairs (4) (4*q+14) (q-2) ∪
  {(q+3,4*q+8)} ∪
  affinePairs (q+4) (6*q+14) (q-1) ∪
  hingedPairs (2*q+6) (1) (q-1) h ∪
  {(3*q+6,8*q+15)} ∪
  hingedPairs (3*q+7) (1) (q-1) h ∪
  {(4*q+7,8*q+14)} ∪
  {(4*q+9,8*q+17)} ∪
  {(4*q+10,8*q+19)} ∪
  {(4*q+12,8*q+18)} ∪
  {(6*q+11,8*q+13)} ∪
  {(6*q+12,8*q+16)}

def langfordHole11b (q h : ℤ) : Prop :=
  h=1 ∨
  (4*q+11 ≤ h ∧ h ≤ 6*q+9 ∧ (h-(4*q+11))%2=0) ∨
  (6*q+13 ≤ h ∧ h ≤ 8*q+11 ∧ (h-(6*q+13))%2=0)

theorem langfordRows11b_endpoints (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole11b q h) :
    pairEndpoints (langfordRows11b q h) = (Finset.Icc 1 (8*q+19)).erase h := by
  unfold langfordHole11b at hh
  ext x
  simp only [langfordRows11b, pairEndpoints_union, pairEndpoints_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hingedPairs,
    mem_pairEndpoints_affinePairs, mem_pairEndpoints_pivotAffinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hxh : x=h
  · subst x
    rcases hh with hh0 | hh1 | hh2 <;> omega
  · by_cases hxz : x=1
    · subst x
      rcases hh with hh0 | hh1 | hh2 <;> omega
    · simp only [hxz,false_and,or_false]
      clear hh
      omega

theorem langfordRows11b_differences (q h : ℤ) (hq : 3 ≤ q) :
    pairDifferences (langfordRows11b q h) = Finset.Icc (2*q+1) (6*q+9) := by
  ext x
  simp only [langfordRows11b, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_union, Finset.mem_singleton, mem_pairDifferences_affinePairs,
    mem_pairDifferences_hingedPairs, Finset.mem_Icc]
  omega

theorem langfordRows11b_card (q h : ℤ) (hq : 3 ≤ q) :
    (langfordRows11b q h).card ≤ (4*q+9).toNat := by
  have hc : (langfordRows11b q h).card ≤ 1+1+(q-2+1).toNat+1+(q-1+1).toNat+(q-1+1).toNat+1+(q-1+1).toNat+1+1+1+1+1+1 := by
    unfold langfordRows11b
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem langfordRows11b_pairing (q h : ℤ) (hq : 3 ≤ q)
    (hh : langfordHole11b q h) :
    LangfordPairing (2*q+1) (6*q+9) h (langfordRows11b q h) := by
  have hh' := hh
  unfold langfordHole11b at hh'
  constructor
  · omega
  · omega
  · omega
  · convert langfordRows11b_endpoints q h hq hh using 1 <;> congr 2 <;> omega
  · exact langfordRows11b_differences q h hq
  · convert langfordRows11b_card q h hq using 1 <;> congr 1 <;> omega

theorem exists_langford_excess6_even (q h : ℤ) (hq : 3 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+11) (hp : h%2=0) :
    ∃ ps, LangfordPairing (2*q) (6*q+4) h ps := by
  have hc : langfordHole2a q h ∨ langfordHole2b q h ∨ langfordHole2a q (8*q+12-h) ∨ langfordHole2b q (8*q+12-h) := by
    simp only [langfordHole2a, langfordHole2b]
    omega
  rcases hc with h0 | h1 | h2 | h3
  · exact ⟨_, langfordRows2a_pairing q h hq h0⟩
  · exact ⟨_, langfordRows2b_pairing q h hq h1⟩
  · have hr := (langfordRows2a_pairing q (8*q+12-h) hq h2).reflect
    refine ⟨reflectPairs (2*((6*q+4)-(2*q)+1)+1)
      (langfordRows2a q (8*q+12-h)), ?_⟩
    convert hr using 1 <;> omega
  · have hr := (langfordRows2b_pairing q (8*q+12-h) hq h3).reflect
    refine ⟨reflectPairs (2*((6*q+4)-(2*q)+1)+1)
      (langfordRows2b q (8*q+12-h)), ?_⟩
    convert hr using 1 <;> omega

theorem exists_langford_excess6_odd (q h : ℤ) (hq : 3 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+15) (hp : h%2=0) :
    ∃ ps, LangfordPairing (2*q+1) (6*q+7) h ps := by
  have hc : langfordHole3a q h ∨ langfordHole3b q h ∨ langfordHole3c q h ∨ langfordHole3a q (8*q+16-h) ∨ langfordHole3b q (8*q+16-h) ∨ langfordHole3c q (8*q+16-h) := by
    simp only [langfordHole3a, langfordHole3b, langfordHole3c]
    omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5
  · exact ⟨_, langfordRows3a_pairing q h hq h0⟩
  · exact ⟨_, langfordRows3b_pairing q h hq h1⟩
  · exact ⟨_, langfordRows3c_pairing q h hq h2⟩
  · have hr := (langfordRows3a_pairing q (8*q+16-h) hq h3).reflect
    refine ⟨reflectPairs (2*((6*q+7)-(2*q+1)+1)+1)
      (langfordRows3a q (8*q+16-h)), ?_⟩
    convert hr using 1 <;> omega
  · have hr := (langfordRows3b_pairing q (8*q+16-h) hq h4).reflect
    refine ⟨reflectPairs (2*((6*q+7)-(2*q+1)+1)+1)
      (langfordRows3b q (8*q+16-h)), ?_⟩
    convert hr using 1 <;> omega
  · have hr := (langfordRows3c_pairing q (8*q+16-h) hq h5).reflect
    refine ⟨reflectPairs (2*((6*q+7)-(2*q+1)+1)+1)
      (langfordRows3c q (8*q+16-h)), ?_⟩
    convert hr using 1 <;> omega

theorem exists_langford_excess7_even (q h : ℤ) (hq : 3 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+13) (hp : h%2=0) :
    ∃ ps, LangfordPairing (2*q) (6*q+5) h ps := by
  have hc : langfordHole6a q h ∨ langfordHole6b q h ∨ langfordHole6a q (8*q+14-h) ∨ langfordHole6b q (8*q+14-h) := by
    simp only [langfordHole6a, langfordHole6b]
    omega
  rcases hc with h0 | h1 | h2 | h3
  · exact ⟨_, langfordRows6a_pairing q h hq h0⟩
  · exact ⟨_, langfordRows6b_pairing q h hq h1⟩
  · have hr := (langfordRows6a_pairing q (8*q+14-h) hq h2).reflect
    refine ⟨reflectPairs (2*((6*q+5)-(2*q)+1)+1)
      (langfordRows6a q (8*q+14-h)), ?_⟩
    convert hr using 1 <;> omega
  · have hr := (langfordRows6b_pairing q (8*q+14-h) hq h3).reflect
    refine ⟨reflectPairs (2*((6*q+5)-(2*q)+1)+1)
      (langfordRows6b q (8*q+14-h)), ?_⟩
    convert hr using 1 <;> omega

theorem exists_langford_excess7_odd (q h : ℤ) (hq : 3 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+17) (hp : h%2=1) :
    ∃ ps, LangfordPairing (2*q+1) (6*q+8) h ps := by
  have hc : langfordHole7a q h ∨ langfordHole7b q h ∨ langfordHole7c q h ∨ langfordHole7a q (8*q+18-h) ∨ langfordHole7b q (8*q+18-h) ∨ langfordHole7c q (8*q+18-h) := by
    simp only [langfordHole7a, langfordHole7b, langfordHole7c]
    omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5
  · exact ⟨_, langfordRows7a_pairing q h hq h0⟩
  · exact ⟨_, langfordRows7b_pairing q h hq h1⟩
  · exact ⟨_, langfordRows7c_pairing q h hq h2⟩
  · have hr := (langfordRows7a_pairing q (8*q+18-h) hq h3).reflect
    refine ⟨reflectPairs (2*((6*q+8)-(2*q+1)+1)+1)
      (langfordRows7a q (8*q+18-h)), ?_⟩
    convert hr using 1 <;> omega
  · have hr := (langfordRows7b_pairing q (8*q+18-h) hq h4).reflect
    refine ⟨reflectPairs (2*((6*q+8)-(2*q+1)+1)+1)
      (langfordRows7b q (8*q+18-h)), ?_⟩
    convert hr using 1 <;> omega
  · have hr := (langfordRows7c_pairing q (8*q+18-h) hq h5).reflect
    refine ⟨reflectPairs (2*((6*q+8)-(2*q+1)+1)+1)
      (langfordRows7c q (8*q+18-h)), ?_⟩
    convert hr using 1 <;> omega

theorem exists_langford_excess8_even (q h : ℤ) (hq : 3 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+15) (hp : h%2=1) :
    ∃ ps, LangfordPairing (2*q) (6*q+6) h ps := by
  have hc : langfordHole10a q h ∨ langfordHole10b q h ∨ langfordHole10a q (8*q+16-h) ∨ langfordHole10b q (8*q+16-h) := by
    simp only [langfordHole10a, langfordHole10b]
    omega
  rcases hc with h0 | h1 | h2 | h3
  · exact ⟨_, langfordRows10a_pairing q h hq h0⟩
  · exact ⟨_, langfordRows10b_pairing q h hq h1⟩
  · have hr := (langfordRows10a_pairing q (8*q+16-h) hq h2).reflect
    refine ⟨reflectPairs (2*((6*q+6)-(2*q)+1)+1)
      (langfordRows10a q (8*q+16-h)), ?_⟩
    convert hr using 1 <;> omega
  · have hr := (langfordRows10b_pairing q (8*q+16-h) hq h3).reflect
    refine ⟨reflectPairs (2*((6*q+6)-(2*q)+1)+1)
      (langfordRows10b q (8*q+16-h)), ?_⟩
    convert hr using 1 <;> omega

theorem exists_langford_excess8_odd (q h : ℤ) (hq : 3 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+19) (hp : h%2=1) :
    ∃ ps, LangfordPairing (2*q+1) (6*q+9) h ps := by
  have hc : langfordHole11a q h ∨ langfordHole11b q h ∨ langfordHole11a q (8*q+20-h) ∨ langfordHole11b q (8*q+20-h) := by
    simp only [langfordHole11a, langfordHole11b]
    omega
  rcases hc with h0 | h1 | h2 | h3
  · exact ⟨_, langfordRows11a_pairing q h hq h0⟩
  · exact ⟨_, langfordRows11b_pairing q h hq h1⟩
  · have hr := (langfordRows11a_pairing q (8*q+20-h) hq h2).reflect
    refine ⟨reflectPairs (2*((6*q+9)-(2*q+1)+1)+1)
      (langfordRows11a q (8*q+20-h)), ?_⟩
    convert hr using 1 <;> omega
  · have hr := (langfordRows11b_pairing q (8*q+20-h) hq h3).reflect
    refine ⟨reflectPairs (2*((6*q+9)-(2*q+1)+1)+1)
      (langfordRows11b q (8*q+20-h)), ?_⟩
    convert hr using 1 <;> omega

/-- Every admissible prescribed hole for excess 6, defect at least 6. -/
theorem exists_langford_excess6 (d h : ℤ) (hd : 6 ≤ d)
    (hh : 1 ≤ h ∧ h ≤ 4*d+11) (hp : h%2=0) :
    ∃ ps, LangfordPairing d (3*d+4) h ps := by
  obtain ⟨q,hq,hde⟩ : ∃ q : ℤ, 3 ≤ q ∧ (d=2*q ∨ d=2*q+1) := by
    refine ⟨d/2, ?_, ?_⟩ <;> omega
  rcases hde with hde | hde
  · obtain ⟨ps,hps⟩ := exists_langford_excess6_even q h hq (by omega) (by omega)
    refine ⟨ps, ?_⟩
    convert hps using 1 <;> omega
  · obtain ⟨ps,hps⟩ := exists_langford_excess6_odd q h hq (by omega) (by omega)
    refine ⟨ps, ?_⟩
    convert hps using 1 <;> omega

/-- Every admissible prescribed hole for excess 7, defect at least 6. -/
theorem exists_langford_excess7 (d h : ℤ) (hd : 6 ≤ d)
    (hh : 1 ≤ h ∧ h ≤ 4*d+13) (hp : h%2=d%2) :
    ∃ ps, LangfordPairing d (3*d+5) h ps := by
  obtain ⟨q,hq,hde⟩ : ∃ q : ℤ, 3 ≤ q ∧ (d=2*q ∨ d=2*q+1) := by
    refine ⟨d/2, ?_, ?_⟩ <;> omega
  rcases hde with hde | hde
  · obtain ⟨ps,hps⟩ := exists_langford_excess7_even q h hq (by omega) (by omega)
    refine ⟨ps, ?_⟩
    convert hps using 1 <;> omega
  · obtain ⟨ps,hps⟩ := exists_langford_excess7_odd q h hq (by omega) (by omega)
    refine ⟨ps, ?_⟩
    convert hps using 1 <;> omega

/-- Every admissible prescribed hole for excess 8, defect at least 6. -/
theorem exists_langford_excess8 (d h : ℤ) (hd : 6 ≤ d)
    (hh : 1 ≤ h ∧ h ≤ 4*d+15) (hp : h%2=1) :
    ∃ ps, LangfordPairing d (3*d+6) h ps := by
  obtain ⟨q,hq,hde⟩ : ∃ q : ℤ, 3 ≤ q ∧ (d=2*q ∨ d=2*q+1) := by
    refine ⟨d/2, ?_, ?_⟩ <;> omega
  rcases hde with hde | hde
  · obtain ⟨ps,hps⟩ := exists_langford_excess8_even q h hq (by omega) (by omega)
    refine ⟨ps, ?_⟩
    convert hps using 1 <;> omega
  · obtain ⟨ps,hps⟩ := exists_langford_excess8_odd q h hq (by omega) (by omega)
    refine ⟨ps, ?_⟩
    convert hps using 1 <;> omega

end
end GN

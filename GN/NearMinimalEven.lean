import GN.Langford

namespace GN
noncomputable section

/-! Four explicit tables for even-defect extended Langford pairings of order 2d.
The coefficients were discovered by finite search. The proofs verify the tables
for every integer q ≥ 4 using only the interval formulas in GN.Langford. -/

def near1EvenLow (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(4*q+2,6*q+2)} ∪
  hingedPairs (2*q+2) 1 (q-2) h ∪
  {(2,3*q+2)} ∪
  affinePairs (3*q+3) (6*q+4) (q-2) ∪
  {(2*q+1,6*q+1)} ∪
  affinePairs 3 (4*q+4) (q-2) ∪
  {(3*q+1,8*q+1)} ∪
  affinePairs (q+2) (6*q+3) (q-2)

set_option maxHeartbeats 0 in
theorem near1EvenLow_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 1 ∨ 4*q+3 ≤ h ∧ h ≤ 6*q-1) (hp : h%2 = 1) :
    pairEndpoints (near1EvenLow q h) = (Finset.Icc 1 (8*q+1)).erase h := by
  ext x
  simp only [near1EvenLow, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 1
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh hp
  omega

set_option maxHeartbeats 0 in
theorem near1EvenLow_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near1EvenLow q h) = Finset.Icc (2*q) (6*q-1) := by
  ext x
  simp only [near1EvenLow, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_singleton, Finset.mem_union, mem_pairDifferences_hingedPairs,
    mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

theorem near1EvenLow_card (q h : ℤ) (hq : 4 ≤ q) :
    (near1EvenLow q h).card ≤ (4*q).toNat := by
  have hc : (near1EvenLow q h).card ≤ (0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat := by
    unfold near1EvenLow hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem near1EvenLow_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 1 ∨ 4*q+3 ≤ h ∧ h ≤ 6*q-1) (hp : h%2 = 1) :
    LangfordPairing (2*q) (6*q-1) h (near1EvenLow q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near1EvenLow_endpoints q h hq hh hp using 1; congr 2; omega
  · exact near1EvenLow_differences q h hq
  · convert near1EvenLow_card q h hq using 1; congr 1; omega

def near1EvenHigh (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(4*q+2,6*q+2)} ∪
  affinePairs (2*q+3) (4*q+4) (q-3) ∪
  {(2,3*q+1)} ∪
  hingedPairs (3*q+3) 3 (q-2) h ∪
  affinePairs 4 (4*q+3) (q-1) ∪
  {(3*q+2,8*q+1)} ∪
  affinePairs (q+4) (6*q+4) (q-2) ∪
  {(1,6*q)}

set_option maxHeartbeats 0 in
theorem near1EvenHigh_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 3 ∨ 6*q+3 ≤ h ∧ h ≤ 8*q-1) (hp : h%2 = 1) :
    pairEndpoints (near1EvenHigh q h) = (Finset.Icc 1 (8*q+1)).erase h := by
  ext x
  simp only [near1EvenHigh, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 3
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh hp
  omega

set_option maxHeartbeats 0 in
theorem near1EvenHigh_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near1EvenHigh q h) = Finset.Icc (2*q) (6*q-1) := by
  ext x
  simp only [near1EvenHigh, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_singleton, Finset.mem_union, mem_pairDifferences_hingedPairs,
    mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

theorem near1EvenHigh_card (q h : ℤ) (hq : 4 ≤ q) :
    (near1EvenHigh q h).card ≤ (4*q).toNat := by
  have hc : (near1EvenHigh q h).card ≤ (0+1 : ℤ).toNat+(q-3+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat := by
    unfold near1EvenHigh hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem near1EvenHigh_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 3 ∨ 6*q+3 ≤ h ∧ h ≤ 8*q-1) (hp : h%2 = 1) :
    LangfordPairing (2*q) (6*q-1) h (near1EvenHigh q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near1EvenHigh_endpoints q h hq hh hp using 1; congr 2; omega
  · exact near1EvenHigh_differences q h hq
  · convert near1EvenHigh_card q h hq using 1; congr 1; omega

def near1EvenGap (q _h : ℤ) : Finset (ℤ × ℤ) :=
  {(6*q+1,8*q+1)} ∪
  affinePairs (2*q+2) (4*q+3) (q-2) ∪
  {(q+1,4*q+1)} ∪
  affinePairs (3*q+1) (6*q+2) (q-1) ∪
  affinePairs 1 (4*q+2) (q-1) ∪
  affinePairs (q+2) (6*q+3) (q-2)

set_option maxHeartbeats 0 in
theorem near1EvenGap_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2*q+1) (hp : h%2 = 1) :
    pairEndpoints (near1EvenGap q h) = (Finset.Icc 1 (8*q+1)).erase h := by
  ext x
  simp only [near1EvenGap, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2*q+1
  · subst x
    omega
  clear hh hp
  omega

set_option maxHeartbeats 0 in
theorem near1EvenGap_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near1EvenGap q h) = Finset.Icc (2*q) (6*q-1) := by
  ext x
  simp only [near1EvenGap, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_singleton, Finset.mem_union, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

theorem near1EvenGap_card (q h : ℤ) (hq : 4 ≤ q) :
    (near1EvenGap q h).card ≤ (4*q).toNat := by
  have hc : (near1EvenGap q h).card ≤ (0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(q-2+1 : ℤ).toNat := by
    unfold near1EvenGap
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem near1EvenGap_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2*q+1) (hp : h%2 = 1) :
    LangfordPairing (2*q) (6*q-1) h (near1EvenGap q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near1EvenGap_endpoints q h hq hh hp using 1; congr 2; omega
  · exact near1EvenGap_differences q h hq
  · convert near1EvenGap_card q h hq using 1; congr 1; omega

def near1EvenCenter (q _h : ℤ) : Finset (ℤ × ℤ) :=
  {(6*q+1,8*q+1)} ∪
  affinePairs (2*q+2) (4*q+3) (q-2) ∪
  {(1,3*q+1)} ∪
  affinePairs (3*q+2) (6*q+3) (q-2) ∪
  affinePairs 2 (4*q+2) (2*q-1)

set_option maxHeartbeats 0 in
theorem near1EvenCenter_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 4*q+1) (_hp : h%2 = 1) :
    pairEndpoints (near1EvenCenter q h) = (Finset.Icc 1 (8*q+1)).erase h := by
  ext x
  simp only [near1EvenCenter, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 4*q+1
  · subst x
    omega
  clear hh _hp
  omega

set_option maxHeartbeats 0 in
theorem near1EvenCenter_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near1EvenCenter q h) = Finset.Icc (2*q) (6*q-1) := by
  ext x
  simp only [near1EvenCenter, pairDifferences_union, pairDifferences_singleton,
    Finset.mem_singleton, Finset.mem_union, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

theorem near1EvenCenter_card (q h : ℤ) (hq : 4 ≤ q) :
    (near1EvenCenter q h).card ≤ (4*q).toNat := by
  have hc : (near1EvenCenter q h).card ≤ (0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(2*q-1+1 : ℤ).toNat := by
    unfold near1EvenCenter
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

theorem near1EvenCenter_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 4*q+1) (hp : h%2 = 1) :
    LangfordPairing (2*q) (6*q-1) h (near1EvenCenter q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near1EvenCenter_endpoints q h hq hh hp using 1; congr 2; omega
  · exact near1EvenCenter_differences q h hq
  · convert near1EvenCenter_card q h hq using 1; congr 1; omega

/-- Every odd hole in the upper half is covered by one of the four tables. -/
theorem near1_even_upper_exists {q h : ℤ} (hq : 4 ≤ q)
    (hh : 4*q+1 ≤ h ∧ h ≤ 8*q+1) (hp : h%2 = 1) :
    ∃ ps, LangfordPairing (2*q) (6*q-1) h ps := by
  by_cases hc : h = 4*q+1
  · exact ⟨_, near1EvenCenter_pairing q h hq hc hp⟩
  by_cases hl : h ≤ 6*q-1
  · exact ⟨_, near1EvenLow_pairing q h hq (by omega) hp⟩
  by_cases hg : h = 6*q+1
  · have hb := near1EvenGap_pairing q (2*q+1) hq rfl (by omega)
    have hr := hb.reflect
    have he : 2*((6*q-1)-(2*q)+1)+2-(2*q+1) = h := by omega
    rw [he] at hr
    exact ⟨_, hr⟩
  by_cases ht : h ≤ 8*q-1
  · exact ⟨_, near1EvenHigh_pairing q h hq (by omega) hp⟩
  · have hb := near1EvenLow_pairing q 1 hq (by omega) (by omega)
    have hr := hb.reflect
    have he : 2*((6*q-1)-(2*q)+1)+2-1 = h := by omega
    rw [he] at hr
    exact ⟨_, hr⟩

/-- Explicit even-defect extended Langford pairings at every admissible hole. -/
theorem near1_even_exists {q h : ℤ} (hq : 4 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+1) (hp : h%2 = 1) :
    ∃ ps, LangfordPairing (2*q) (6*q-1) h ps := by
  by_cases hu : 4*q+1 ≤ h
  · exact near1_even_upper_exists hq ⟨hu,hh.2⟩ hp
  · obtain ⟨ps, hps⟩ := near1_even_upper_exists (q := q) (h := 8*q+2-h)
      hq (by omega) (by omega)
    have hr := hps.reflect
    have he : 2*((6*q-1)-(2*q)+1)+2-(8*q+2-h) = h := by ring
    rw [he] at hr
    exact ⟨_, hr⟩

end
end GN

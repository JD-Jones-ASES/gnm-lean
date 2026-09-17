import GN.Langford

namespace GN
noncomputable section

/-- The minimal extended Langford table. The first row pivots into position1
when the requested hole lies among its odd second endpoints. -/
def minimalLangfordPairs (d h : ℤ) : Finset (ℤ × ℤ) :=
  hingedPairs (d+1) 1 (d-1) h ∪ affinePairs 2 (2*d+2) (d-2)

 theorem minimalLangford_endpoints {d h : ℤ} (hd : 1 ≤ d)
    (hh : h = 1 ∨ 2*d+1 ≤ h ∧ h ≤ 4*d-1) (hodd : h%2 = 1) :
    pairEndpoints (minimalLangfordPairs d h) = (Finset.Icc 1 (4*d-1)).erase h := by
  ext x
  simp only [minimalLangfordPairs, pairEndpoints_union, hingedPairs,
    Finset.mem_union, mem_pairEndpoints_pivotAffinePairs,
    mem_pairEndpoints_affinePairs, Finset.mem_erase, Finset.mem_Icc]
  omega

 theorem minimalLangford_differences (d h : ℤ) (_hd : 1 ≤ d) :
    pairDifferences (minimalLangfordPairs d h) = Finset.Icc d (3*d-2) := by
  ext x
  simp only [minimalLangfordPairs, pairDifferences_union, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

 theorem minimalLangford_card (d h : ℤ) (hd : 1 ≤ d) :
    (minimalLangfordPairs d h).card ≤ (2*d-1).toNat := by
  have hc : (minimalLangfordPairs d h).card ≤ (d-1+1).toNat+(d-2+1).toNat := by
    unfold minimalLangfordPairs hingedPairs
    exact card_union_le_of_le (card_pivotAffinePairs_le _ _ _ _ _)
      (card_affinePairs_le _ _ _)
  omega

 theorem minimalLangford_pairing {d h : ℤ} (hd : 1 ≤ d)
    (hh : h = 1 ∨ 2*d+1 ≤ h ∧ h ≤ 4*d-1) (hodd : h%2 = 1) :
    LangfordPairing d (3*d-2) h (minimalLangfordPairs d h) := by
  constructor
  · exact hd
  · omega
  · omega
  · convert minimalLangford_endpoints hd hh hodd using 1; congr 2; omega
  · exact minimalLangford_differences d h hd
  · convert minimalLangford_card d h hd using 1; congr 1; omega

/-- Every odd hole has a minimal pairing with differences d,...,3d-2. -/
 theorem exists_minimal_langford {d h : ℤ} (hd : 1 ≤ d)
    (hh : 1 ≤ h ∧ h ≤ 4*d-1) (hodd : h%2 = 1) :
    ∃ ps, LangfordPairing d (3*d-2) h ps := by
  by_cases hhigh : h = 1 ∨ 2*d+1 ≤ h
  · exact ⟨_, minimalLangford_pairing hd (by omega) hodd⟩
  · have hr : 2*d+1 ≤ 4*d-h ∧ 4*d-h ≤ 4*d-1 := by omega
    have ho : (4*d-h)%2 = 1 := by omega
    have hp := (minimalLangford_pairing hd (Or.inr hr) ho).reflect
    have he : 2*(3*d-2-d+1)+2-(4*d-h) = h := by omega
    rw [he] at hp
    exact ⟨_, hp⟩

end
end GN

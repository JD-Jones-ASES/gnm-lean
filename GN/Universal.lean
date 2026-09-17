import GN.Existence
import GN.NearMinimal
import GN.NearMinimalEven
import GN.LangfordTables
import GN.SmallPermutations

namespace GN
noncomputable section

/-- The excess-one family for all defects d≥8 and every allowed hole. -/
theorem exists_near1_langford {d h : ℤ} (hd : 8 ≤ d)
    (hh : 1 ≤ h ∧ h ≤ 4*d+1) (hp : h%2 = (d+1)%2) :
    ∃ ps, LangfordPairing d (3*d-1) h ps := by
  let q := d/2
  have hq : 4 ≤ q := by dsimp [q]; omega
  have hdq : d = 2*q ∨ d = 2*q+1 := by dsimp [q]; omega
  rcases hdq with he | he
  · obtain ⟨ps, hps⟩ := near1_even_exists (q := q) (h := h) hq (by omega) (by omega)
    have hk : 6*q-1 = 3*d-1 := by omega
    rw [← he, hk] at hps
    exact ⟨ps, hps⟩
  · obtain ⟨ps, hps⟩ := near1_odd_exists (q := q) (h := h) hq (by omega) (by omega)
    have hk : 6*q+2 = 3*d-1 := by omega
    rw [← he, hk] at hps
    exact ⟨ps, hps⟩

theorem near1_langford_family : LangfordFamily 8 1 (fun d => d+1) := by
  intro d hd h hh hp
  dsimp at hp
  obtain ⟨ps, hps⟩ := exists_near1_langford (h := h) hd (by omega) hp
  refine ⟨ps, ?_⟩
  convert hps using 1; omega

theorem near2_langford_family : LangfordFamily 8 2 (fun _ => 0) := by
  intro d hd h hh hp
  dsimp at hp
  obtain ⟨ps, hps⟩ := exists_near2_langford (h := h) hd (by omega) (by omega)
  refine ⟨ps, ?_⟩
  convert hps using 1; omega

theorem excess6_langford_family : LangfordFamily 6 6 (fun _ => 0) := by
  intro d hd h hh hp
  dsimp at hp
  obtain ⟨ps, hps⟩ := exists_langford_excess6 d h hd (by omega) (by omega)
  refine ⟨ps, ?_⟩
  convert hps using 1; omega

theorem excess7_langford_family : LangfordFamily 6 7 (fun d => d) := by
  intro d hd h hh hp
  dsimp at hp
  obtain ⟨ps, hps⟩ := exists_langford_excess7 d h hd (by omega) hp
  refine ⟨ps, ?_⟩
  convert hps using 1; omega

theorem excess8_langford_family : LangfordFamily 6 8 (fun _ => 1) := by
  intro d hd h hh hp
  dsimp at hp
  obtain ⟨ps, hps⟩ := exists_langford_excess8 d h hd (by omega) (by omega)
  refine ⟨ps, ?_⟩
  convert hps using 1; omega

/-- Every prescribed missing position has a permutation whose differences are
exactly ±1,...,±k. All finite certificates and unbounded families are proved. -/
theorem displacement_permutations {k j : ℤ} (hk : 3 ≤ k)
    (hj : -k ≤ j ∧ j ≤ k) :
    ∃ σ : ℤ → ℤ, DisplacementPermutation k j σ := by
  by_cases hs : k ≤ 21
  · exact bounded_displacement_permutations hk hs hj
  · exact displacement_permutations_of_langford_families
      (minimal_langford_family.mono (by omega))
      near1_langford_family near2_langford_family excess6_langford_family
      excess7_langford_family excess8_langford_family (by omega) hj

end
end GN

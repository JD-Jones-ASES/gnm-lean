import GN.Signed

namespace GN

/-- Explicit base permutations of positions `1,...,2k+1`, fixing position `h`.
The forty rows cover `k=3,4,5,6` and every position. Their correctness is
established below by kernel-checked finite arithmetic, not by an external
search or a runtime data source. Values outside these forty rows are irrelevant.
-/
def finitePermutationValues : ℕ → ℕ → List ℤ
  | 3, 1 => [1, 5, 2, 6, 3, 7, 4]
  | 3, 2 => [4, 2, 1, 5, 7, 3, 6]
  | 3, 3 => [4, 1, 3, 6, 2, 7, 5]
  | 3, 4 => [2, 1, 6, 4, 7, 3, 5]
  | 3, 5 => [2, 4, 1, 7, 5, 3, 6]
  | 3, 6 => [2, 1, 5, 7, 3, 6, 4]
  | 3, 7 => [4, 1, 5, 2, 6, 3, 7]
  | 4, 1 => [1, 4, 2, 8, 6, 9, 3, 5, 7]
  | 4, 2 => [4, 2, 1, 6, 9, 7, 3, 5, 8]
  | 4, 3 => [4, 1, 3, 8, 7, 2, 5, 9, 6]
  | 4, 4 => [2, 1, 7, 4, 8, 3, 9, 6, 5]
  | 4, 5 => [3, 1, 7, 2, 5, 9, 8, 4, 6]
  | 4, 6 => [3, 5, 2, 1, 9, 6, 8, 4, 7]
  | 4, 7 => [4, 3, 2, 1, 9, 8, 7, 6, 5]
  | 4, 8 => [2, 1, 5, 7, 9, 4, 3, 8, 6]
  | 4, 9 => [3, 1, 7, 5, 8, 2, 4, 6, 9]
  | 5, 1 => [1, 4, 2, 5, 9, 11, 10, 3, 6, 8, 7]
  | 5, 2 => [4, 2, 1, 5, 10, 8, 11, 3, 6, 9, 7]
  | 5, 3 => [4, 1, 3, 5, 9, 11, 2, 10, 6, 8, 7]
  | 5, 4 => [2, 1, 5, 4, 9, 11, 10, 3, 6, 8, 7]
  | 5, 5 => [2, 1, 7, 9, 5, 3, 10, 4, 11, 8, 6]
  | 5, 6 => [3, 1, 8, 2, 9, 6, 4, 11, 10, 5, 7]
  | 5, 7 => [4, 3, 1, 8, 2, 11, 7, 10, 5, 9, 6]
  | 5, 8 => [2, 4, 1, 3, 9, 11, 10, 8, 5, 7, 6]
  | 5, 9 => [2, 1, 5, 8, 3, 11, 10, 4, 9, 7, 6]
  | 5, 10 => [2, 1, 6, 8, 3, 11, 9, 5, 4, 10, 7]
  | 5, 11 => [3, 1, 4, 8, 10, 9, 2, 5, 7, 6, 11]
  | 6, 1 => [1, 4, 2, 5, 10, 12, 11, 6, 3, 13, 7, 9, 8]
  | 6, 2 => [4, 2, 1, 5, 11, 10, 6, 13, 3, 12, 7, 9, 8]
  | 6, 3 => [4, 1, 3, 5, 9, 11, 13, 2, 6, 12, 7, 10, 8]
  | 6, 4 => [2, 1, 5, 4, 10, 12, 11, 6, 3, 13, 7, 9, 8]
  | 6, 5 => [2, 1, 7, 10, 5, 3, 12, 4, 11, 13, 9, 6, 8]
  | 6, 6 => [2, 1, 8, 10, 3, 6, 11, 4, 12, 5, 13, 9, 7]
  | 6, 7 => [4, 1, 9, 2, 10, 3, 7, 12, 11, 6, 5, 13, 8]
  | 6, 8 => [2, 4, 7, 1, 3, 11, 13, 8, 12, 5, 10, 6, 9]
  | 6, 9 => [3, 5, 2, 1, 10, 4, 13, 12, 9, 11, 6, 8, 7]
  | 6, 10 => [3, 1, 6, 5, 2, 11, 13, 12, 4, 10, 9, 8, 7]
  | 6, 11 => [2, 4, 1, 3, 10, 9, 13, 12, 5, 7, 11, 6, 8]
  | 6, 12 => [2, 1, 6, 9, 3, 10, 13, 4, 11, 5, 8, 12, 7]
  | 6, 13 => [3, 1, 4, 9, 11, 10, 5, 2, 12, 6, 8, 7, 13]
  | _, _ => []

/-- Translate a position permutation into the centered integer interval.
The value outside the relevant domain is arbitrary and is never used.
-/
def finitePermutation (k j u : ℤ) : ℤ :=
  (finitePermutationValues k.toNat (j+k+1).toNat).getD (u+k).toNat 0 - (k+1)

/-- A finite-image certificate suffices to prove both required bijections. -/
theorem displacementPermutation_of_images {k j : ℤ} {σ : ℤ → ℤ}
    (hσ : (displacementDomain k j).image σ = displacementDomain k j)
    (hδ : (displacementDomain k j).image (fun u => σ u-u) =
      (Finset.Icc (-k) k).erase 0)
    (hc : (displacementDomain k j).card ≤ ((Finset.Icc (-k) k).erase 0).card) :
    DisplacementPermutation k j σ := by
  constructor
  · exact (Finset.image_eq_iff_bijOn_of_card le_rfl).mp hσ
  · exact (Finset.image_eq_iff_bijOn_of_card hc).mp hδ

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The complete finite certificate checks image coverage and cardinality.
This proof uses ordinary `decide`, whose proof term is checked by Lean's kernel.
-/
private theorem finite_permutation_certificates :
    ∀ k ∈ (Finset.Icc 3 6 : Finset ℤ),
      ∀ j ∈ Finset.Icc (-k) k,
        (displacementDomain k j).image (finitePermutation k j) =
          displacementDomain k j ∧
        (displacementDomain k j).image (fun u => finitePermutation k j u-u) =
          (Finset.Icc (-k) k).erase 0 ∧
        (displacementDomain k j).card ≤ ((Finset.Icc (-k) k).erase 0).card := by
  decide

/-- Every prescribed hole has a displacement permutation in the forty base cases. -/
theorem finite_displacement_permutations {k j : ℤ} (hk : 3 ≤ k) (hk' : k ≤ 6)
    (hj : -k ≤ j ∧ j ≤ k) : ∃ σ : ℤ → ℤ, DisplacementPermutation k j σ := by
  obtain ⟨hσ, hδ, hc⟩ := finite_permutation_certificates k
    (Finset.mem_Icc.mpr ⟨hk, hk'⟩) j (Finset.mem_Icc.mpr hj)
  exact ⟨finitePermutation k j, displacementPermutation_of_images hσ hδ hc⟩

end GN

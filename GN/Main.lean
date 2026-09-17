import GN.Induction
import GN.Small
import GN.Universal

namespace GN
noncomputable section

/-- The remaining unbounded permutation input implies the full partition theorem.
This bridge is not the unconditional final theorem. -/
theorem gurvich_naumova_of_displacement_permutations
    (hperm : ∀ k : ℤ, 3 ≤ k → ∀ j : ℤ, -k ≤ j ∧ j ≤ k →
      ∃ σ : ℤ → ℤ, DisplacementPermutation k j σ) :
    ∀ n : ℕ, HasGood (interval n) := by
  apply hasGood_all_of_critical
  intro P r t hP hPr hmod hs
  by_cases hr : r < 11
  · exact critical_small_extension hP hPr hr hmod
  · exact critical_large_of_permutations hperm hP hPr (by omega) hmod hs

/-- The Gurvich–Naumova partition conjecture for powers of three, including
    the empty interval. This theorem has no unproved construction hypothesis. -/
theorem gurvich_naumova (n : ℕ) : HasGood (interval n) := by
  apply gurvich_naumova_of_displacement_permutations
  intro k hk j hj
  exact displacement_permutations hk hj

end
end GN

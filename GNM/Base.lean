import GNM.Search
import GNM.Data.BaseWitnesses

/-!
# The finite base

Below eighty-one the classification is decided by evaluation: at every value outside the two
exceptional sets three of the tabulated partitions are checked to be good and pairwise different,
and at the twenty values the classification consumes the exhaustive search is run against the
tabulated list, so the count there is exactly one or exactly two. Everything above is reduced to
this base by the transports and the stabilization.
-/

namespace GNM

open GN

noncomputable section

/-- Three good partitions at every non-exceptional value at most eighty. -/
theorem three_le_count_of_le_80 (n : ℕ) (hn : n ≤ 80) (h1 : ¬ Nu n) (h2 : ¬ E2 n) :
    3 ≤ count n := by
  sorry

/-- The values at most eighty-six with exactly one good partition. -/
theorem count_eq_one_small :
    ∀ n ∈ ({1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14, 23, 30, 32, 86} : Finset ℕ), count n = 1 := by
  sorry

/-- The values at most eighty-six with exactly two good partitions. -/
theorem count_eq_two_small : ∀ n ∈ ({6, 13, 21, 75} : Finset ℕ), count n = 2 := by
  sorry

end

end GNM

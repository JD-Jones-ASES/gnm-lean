import GNM.Positive
import GNM.Negative
import GNM.Stabilize
import GNM.Base

/-!
# The assembly

Every interval is placed in one of two regimes by the power of three nearest below it: either it
lies in the lower half of the gap, where it is a power plus a small offset, or in the upper half,
where it is the next power minus a small offset. In the first regime the frames give three
partitions at every offset outside the exceptional list; in the second, the count at the offset
minus one is a lower bound, and when that is itself exceptional the two gadgets take over. The exact
counts on the two exceptional sets come from the finite base, transported along each family by the
stabilization.
-/

namespace GNM

open GN

noncomputable section

/-- Every interval outside the two exceptional sets has at least three good partitions. -/
theorem three_le_count_of_not_exceptional (n : ℕ) (hn : 1 ≤ n) (h1 : ¬ Nu n) (h2 : ¬ E2 n) :
    3 ≤ count n := by
  sorry

/-- Every member of the first exceptional set has exactly one good partition. -/
theorem count_eq_one_of_nu {n : ℕ} (h : Nu n) : count n = 1 := by
  sorry

/-- Every member of the second exceptional set has exactly two good partitions. -/
theorem count_eq_two_of_e2 {n : ℕ} (h : E2 n) : count n = 2 := by
  sorry

end

end GNM

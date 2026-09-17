import GNM.Lift

/-!
# The counts are constant along each family

Above the threshold the lift and the truncation are mutually inverse, so the good partitions at a
fixed offset from two different powers of three are in bijection and the counts agree. Every value
of the two exceptional sets lies on such a family, which is how twenty exact counts at small values
decide the count at every member.
-/

namespace GNM

open GN

noncomputable section

/-- The count at a negative offset is the same at every admissible power. -/
theorem count_sub_eq {r t t' : ℕ} (hr : 1 ≤ r) (hthr : r * (r - 1) < 3 ^ t) (h2 : 2 * r < 3 ^ t)
    (htt' : t ≤ t') : count (3 ^ t - r) = count (3 ^ t' - r) := by
  sorry

/-- The count at a positive offset is the same at every admissible power. -/
theorem count_add_eq {r t t' : ℕ} (hthr : r * (r + 1) < 3 ^ t) (htt' : t ≤ t') :
    count (3 ^ t + r) = count (3 ^ t' + r) := by
  sorry

end

end GNM

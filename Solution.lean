import GNM.Main

namespace GNM

/-- `{1, …, n}` has exactly one good partition if and only if `n ∈ N_u`. -/
theorem count_eq_one_iff (n : ℕ) (hn : 1 ≤ n) : count n = 1 ↔ Nu n :=
  count_eq_one_iff_internal n hn

/-- `{1, …, n}` has exactly two good partitions if and only if `n ∈ E_2`. -/
theorem count_eq_two_iff (n : ℕ) : count n = 2 ↔ E2 n :=
  count_eq_two_iff_internal n

/-- `{1, …, n}` has at least three good partitions if and only if `n` lies in neither `N_u` nor
`E_2`. -/
theorem three_le_count_iff (n : ℕ) (hn : 1 ≤ n) : 3 ≤ count n ↔ ¬ Nu n ∧ ¬ E2 n :=
  three_le_count_iff_internal n hn

/-- For every `t ≥ 3`, `{1, …, 3^t − 6}` has exactly two good partitions. -/
theorem count_eq_two_of_add_six (n t : ℕ) (ht : 3 ≤ t) (h : n + 6 = 3 ^ t) : count n = 2 :=
  count_eq_two_of_add_six_internal n t ht h

end GNM

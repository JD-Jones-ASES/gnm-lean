import GNM.Search
import GNM.SearchFacts

/-!
# The finite base

At the tabulated values the classification is decided by evaluation. At every value outside the two
exceptional sets, three of the tabulated partitions are good partitions of the interval and no two
of them are equal, so the count is at least three; and at the twenty values whose exact count the
classification consumes, the exhaustive search run against the tabulated list shows that the list is
all of the good partitions, so the count is exactly one or exactly two. Everything above this range
is reduced to it by the transports and by the stabilization along each family.

The kernel-checked facts live in a module that imports no library at all; this one only reads them
off and feeds them to the bridges, and evaluates nothing itself. The range at most eighty is taken
in blocks of ten, one auxiliary statement each, because a single case analysis over all eighty
values is more than one declaration can carry.
-/

namespace GNM

open GN

/-- Three tabulated partitions, good and pairwise different, give a count of at least three. -/
theorem three_le_count_of_threeOK {n : ℕ} (h : threeOK n = true) : 3 ≤ count n := by
  obtain ⟨c0, c1, c2, d01, d02, d12⟩ := threeOK_facts h
  exact three_le_count_of_witnesses c0 c1 c2 d01 d02 d12

/-- One good tabulated partition and an accepting search give a count of one. -/
theorem count_eq_one_of_oneOK {n : ℕ} (hn : 3 * n < 729) (h : oneOK n = true)
    (hs : search n [wAt n 0] = true) : count n = 1 :=
  count_eq_one_of_search hn h hs

/-- Two good, different tabulated partitions and an accepting search give a count of two. -/
theorem count_eq_two_of_twoOK {n : ℕ} (hn : 3 * n < 729) (h : twoOK n = true)
    (hs : search n [wAt n 0, wAt n 1] = true) : count n = 2 := by
  obtain ⟨c0, c1, d01⟩ := twoOK_facts h
  exact count_eq_two_of_search hn c0 c1 d01 hs

/-- Three good partitions at every value from 1 to 10 outside the two exceptional sets. -/
private theorem three_le_count_of_le_10 (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  rw [nu_iff_of_le n (by omega)] at h1
  rw [e2_iff_of_le n (by omega)] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
  interval_cases n
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- Three good partitions at every value from 11 to 20 outside the two exceptional sets. -/
private theorem three_le_count_of_le_20 (n : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 20)
    (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  rw [nu_iff_of_le n (by omega)] at h1
  rw [e2_iff_of_le n (by omega)] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
  interval_cases n
  · omega
  · omega
  · omega
  · omega
  · exact three_le_count_of_threeOK three_ok_15
  · exact three_le_count_of_threeOK three_ok_16
  · exact three_le_count_of_threeOK three_ok_17
  · exact three_le_count_of_threeOK three_ok_18
  · exact three_le_count_of_threeOK three_ok_19
  · exact three_le_count_of_threeOK three_ok_20

/-- Three good partitions at every value from 21 to 30 outside the two exceptional sets. -/
private theorem three_le_count_of_le_30 (n : ℕ) (hlo : 21 ≤ n) (hhi : n ≤ 30)
    (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  rw [nu_iff_of_le n (by omega)] at h1
  rw [e2_iff_of_le n (by omega)] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
  interval_cases n
  · omega
  · exact three_le_count_of_threeOK three_ok_22
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- Three good partitions at every value from 31 to 40 outside the two exceptional sets. -/
private theorem three_le_count_of_le_40 (n : ℕ) (hlo : 31 ≤ n) (hhi : n ≤ 40)
    (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  rw [nu_iff_of_le n (by omega)] at h1
  rw [e2_iff_of_le n (by omega)] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
  interval_cases n
  · exact three_le_count_of_threeOK three_ok_31
  · omega
  · exact three_le_count_of_threeOK three_ok_33
  · exact three_le_count_of_threeOK three_ok_34
  · exact three_le_count_of_threeOK three_ok_35
  · exact three_le_count_of_threeOK three_ok_36
  · exact three_le_count_of_threeOK three_ok_37
  · exact three_le_count_of_threeOK three_ok_38
  · exact three_le_count_of_threeOK three_ok_39
  · exact three_le_count_of_threeOK three_ok_40

/-- Three good partitions at every value from 41 to 50 outside the two exceptional sets. -/
private theorem three_le_count_of_le_50 (n : ℕ) (hlo : 41 ≤ n) (hhi : n ≤ 50)
    (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  rw [nu_iff_of_le n (by omega)] at h1
  rw [e2_iff_of_le n (by omega)] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
  interval_cases n
  · exact three_le_count_of_threeOK three_ok_41
  · exact three_le_count_of_threeOK three_ok_42
  · exact three_le_count_of_threeOK three_ok_43
  · exact three_le_count_of_threeOK three_ok_44
  · exact three_le_count_of_threeOK three_ok_45
  · exact three_le_count_of_threeOK three_ok_46
  · exact three_le_count_of_threeOK three_ok_47
  · exact three_le_count_of_threeOK three_ok_48
  · exact three_le_count_of_threeOK three_ok_49
  · exact three_le_count_of_threeOK three_ok_50

/-- Three good partitions at every value from 51 to 60 outside the two exceptional sets. -/
private theorem three_le_count_of_le_60 (n : ℕ) (hlo : 51 ≤ n) (hhi : n ≤ 60)
    (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  rw [nu_iff_of_le n (by omega)] at h1
  rw [e2_iff_of_le n (by omega)] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
  interval_cases n
  · exact three_le_count_of_threeOK three_ok_51
  · exact three_le_count_of_threeOK three_ok_52
  · exact three_le_count_of_threeOK three_ok_53
  · exact three_le_count_of_threeOK three_ok_54
  · exact three_le_count_of_threeOK three_ok_55
  · exact three_le_count_of_threeOK three_ok_56
  · exact three_le_count_of_threeOK three_ok_57
  · exact three_le_count_of_threeOK three_ok_58
  · exact three_le_count_of_threeOK three_ok_59
  · exact three_le_count_of_threeOK three_ok_60

/-- Three good partitions at every value from 61 to 70 outside the two exceptional sets. -/
private theorem three_le_count_of_le_70 (n : ℕ) (hlo : 61 ≤ n) (hhi : n ≤ 70)
    (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  rw [nu_iff_of_le n (by omega)] at h1
  rw [e2_iff_of_le n (by omega)] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
  interval_cases n
  · exact three_le_count_of_threeOK three_ok_61
  · exact three_le_count_of_threeOK three_ok_62
  · exact three_le_count_of_threeOK three_ok_63
  · exact three_le_count_of_threeOK three_ok_64
  · exact three_le_count_of_threeOK three_ok_65
  · exact three_le_count_of_threeOK three_ok_66
  · exact three_le_count_of_threeOK three_ok_67
  · exact three_le_count_of_threeOK three_ok_68
  · exact three_le_count_of_threeOK three_ok_69
  · exact three_le_count_of_threeOK three_ok_70

/-- Three good partitions at every value from 71 to 80 outside the two exceptional sets. -/
private theorem three_le_count_of_le_80_block (n : ℕ) (hlo : 71 ≤ n) (hhi : n ≤ 80)
    (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  rw [nu_iff_of_le n (by omega)] at h1
  rw [e2_iff_of_le n (by omega)] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
  interval_cases n
  · exact three_le_count_of_threeOK three_ok_71
  · exact three_le_count_of_threeOK three_ok_72
  · exact three_le_count_of_threeOK three_ok_73
  · exact three_le_count_of_threeOK three_ok_74
  · omega
  · exact three_le_count_of_threeOK three_ok_76
  · omega
  · omega
  · omega
  · omega

/-- Three good partitions at every value at least one and at most eighty outside the two
exceptional sets. -/
theorem three_le_count_of_le_80 (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 80) (h1 : ¬ Nu n)
    (h2 : ¬ E2 n) : 3 ≤ count n := by
  by_cases c10 : n ≤ 10
  · exact three_le_count_of_le_10 n (by omega) c10 h1 h2
  by_cases c20 : n ≤ 20
  · exact three_le_count_of_le_20 n (by omega) c20 h1 h2
  by_cases c30 : n ≤ 30
  · exact three_le_count_of_le_30 n (by omega) c30 h1 h2
  by_cases c40 : n ≤ 40
  · exact three_le_count_of_le_40 n (by omega) c40 h1 h2
  by_cases c50 : n ≤ 50
  · exact three_le_count_of_le_50 n (by omega) c50 h1 h2
  by_cases c60 : n ≤ 60
  · exact three_le_count_of_le_60 n (by omega) c60 h1 h2
  by_cases c70 : n ≤ 70
  · exact three_le_count_of_le_70 n (by omega) c70 h1 h2
  exact three_le_count_of_le_80_block n (by omega) hn h1 h2

/-- The sixteen values whose count of one the finite base settles. -/
theorem count_eq_one_small :
    ∀ n ∈ ({1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14, 23, 30, 32, 86} : Finset ℕ),
      count n = 1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_1 search_one_1
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_2 search_one_2
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_3 search_one_3
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_4 search_one_4
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_5 search_one_5
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_7 search_one_7
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_8 search_one_8
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_9 search_one_9
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_10 search_one_10
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_11 search_one_11
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_12 search_one_12
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_14 search_one_14
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_23 search_one_23
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_30 search_one_30
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_32 search_one_32
  · exact count_eq_one_of_oneOK (by norm_num) one_ok_86 search_one_86

/-- The four values whose count of two the finite base settles. -/
theorem count_eq_two_small : ∀ n ∈ ({6, 13, 21, 75} : Finset ℕ), count n = 2 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact count_eq_two_of_twoOK (by norm_num) two_ok_6 search_two_6
  · exact count_eq_two_of_twoOK (by norm_num) two_ok_13 search_two_13
  · exact count_eq_two_of_twoOK (by norm_num) two_ok_21 search_two_21
  · exact count_eq_two_of_twoOK (by norm_num) two_ok_75 search_two_75

end GNM

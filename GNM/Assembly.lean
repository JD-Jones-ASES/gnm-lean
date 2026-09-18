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

/-- One step of the induction: three good partitions at an interval outside the two exceptional
sets, given the same statement at every shorter interval. -/
private theorem three_le_count_step (n : ℕ)
    (ih : ∀ m, m < n → 1 ≤ m → ¬ Nu m → ¬ E2 m → 3 ≤ count m)
    (hn : 1 ≤ n) (h1 : ¬ Nu n) (h2 : ¬ E2 n) : 3 ≤ count n := by
  by_cases hsmall : n ≤ 80
  · exact three_le_count_of_le_80 n hn hsmall h1 h2
  -- Above eighty the interval is measured against the power of three just below it.
  obtain ⟨t, htdef⟩ : ∃ t, t = Nat.log 3 n := ⟨_, rfl⟩
  have hPle : 3 ^ t ≤ n := by
    rw [htdef]
    exact Nat.pow_log_le_self 3 (by omega)
  have hnlt : n < 3 ^ (t + 1) := by
    rw [htdef]
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hlit : (3 : ℕ) ^ 4 = 81 := by norm_num
  have ht4 : 4 ≤ t := by
    by_contra hc
    have hle : (3 : ℕ) ^ (t + 1) ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨P, hP⟩ : ∃ P, P = 3 ^ t := ⟨_, rfl⟩
  have hP81 : 81 ≤ P := by
    have hmono : (3 : ℕ) ^ 4 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht4
    omega
  have hQP : 3 ^ (t + 1) = 3 * P := by
    rw [hP, pow_succ]
    ring
  have hodd : 3 ^ (t + 1) % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rcases Nat.lt_or_ge (2 * n) (3 * P) with hreg | hreg
  · -- The lower half of the gap: the interval is the power plus a small offset.
    obtain ⟨r, hr⟩ : ∃ r, n = P + r := ⟨n - P, by omega⟩
    have hPr : 2 * r < P := by omega
    have hnu : ¬ Nu (3 ^ t + r) := by
      rw [← hP, ← hr]
      exact h1
    have hrnot : ¬ (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5) := fun hc =>
      hnu ((nu_add_iff ht4 (by omega)).mpr hc)
    simp only [not_or] at hrnot
    rw [hr]
    by_cases h4 : r = 4
    · subst h4
      exact three_le_count_add_four hP (by omega)
    by_cases h6 : r = 6
    · subst h6
      exact three_le_count_add_six hP (by omega)
    by_cases h8 : r = 8
    · subst h8
      exact three_le_count_add_eight hP (by omega)
    by_cases hmod : r % 3 = 2
    · exact three_le_count_add_of_threeFrames hP hPr (by omega) hmod
    · exact three_le_count_add_of_threeFrameA hP hPr (by omega)
        (threeFrameA_of_mod (r : ℤ) (by omega) (by omega))
  · -- The upper half of the gap: the interval is the next power minus a small offset.
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = 3 ^ (t + 1) := ⟨_, rfl⟩
    obtain ⟨r, hrQ⟩ : ∃ r, n + r = Q := ⟨Q - n, by omega⟩
    have hr1 : 1 ≤ r := by omega
    have h2r : 2 * r < Q := by omega
    have hrnot : ¬ (r = 1 ∨ r = 2 ∨ r = 4) := fun hc =>
      h1 ((nu_sub_iff (t := t + 1) (by omega) hr1 (by omega) (by omega)).mpr hc)
    have hrnot2 : ¬ (r = 3 ∨ r = 6) := fun hc =>
      h2 ((e2_sub_iff (t := t + 1) (by omega) hr1 (by omega) (by omega)).mpr hc)
    simp only [not_or] at hrnot hrnot2
    have hneq : n = Q - r := by omega
    by_cases hex : Nu (r - 1) ∨ E2 (r - 1)
    · -- The offset below is itself exceptional, and one of the two gadgets applies.
      by_cases hr33 : r ≤ 33
      · -- A small offset is carried up from the fourth power, where the base decides it.
        have hbase : 3 ≤ count (81 - r) := by
          refine three_le_count_of_le_80 (81 - r) (by omega) (by omega) ?_ ?_
          · intro hc
            rw [nu_iff_of_le _ (by omega)] at hc
            simp only [Finset.mem_insert, Finset.mem_singleton] at hc
            omega
          · intro hc
            rw [e2_iff_of_le _ (by omega)] at hc
            simp only [Finset.mem_insert, Finset.mem_singleton] at hc
            omega
        have hstep : count (3 ^ 4 - r) ≤ count (3 ^ (t + 1) - r) :=
          count_sub_le_count_sub hr1 (by omega) (by omega)
        have h81r : (3 : ℕ) ^ 4 - r = 81 - r := by omega
        rw [h81r] at hstep
        rw [hneq, hQ]
        omega
      · -- A large offset carries the normal form of an exceptional value, and the gadgets fire.
        obtain ⟨s, hs4, hform⟩ := exceptional_form (m := r - 1) (by omega) hex
        obtain ⟨R, hR⟩ : ∃ R, R = 3 ^ s := ⟨_, rfl⟩
        have hR81 : 81 ≤ R := by
          have hmono : (3 : ℕ) ^ 4 ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs4
          omega
        rcases hform with ⟨e, he, hem⟩ | ⟨c, hc, hcm⟩
        · have hRQ : R < Q := by omega
          have h3RQ : 3 * R ≤ Q := by
            by_contra hcon
            have heq : t + 1 = s := pow_three_eq_of_lt (t := s) (u := t + 1) (by omega) (by omega)
            rw [heq] at hQ
            omega
          have hne : n = Q - (R - e + 1) := by omega
          rw [hne]
          exact three_le_count_sub_below hR (by omega) he hQ h3RQ
        · have hRQ : R < Q := by omega
          have h3RQ : 3 * R ≤ Q := by
            by_contra hcon
            have heq : t + 1 = s := pow_three_eq_of_lt (t := s) (u := t + 1) (by omega) (by omega)
            rw [heq] at hQ
            omega
          have hne : n = Q - (R + (c + 1)) := by omega
          rw [hne]
          exact three_le_count_sub_above hR (by omega) (by omega) hQ h3RQ
    · -- The offset below is not exceptional, so the induction hypothesis applies there.
      rw [not_or] at hex
      have hbase : 3 ≤ count (r - 1) := ih (r - 1) (by omega) (by omega) hex.1 hex.2
      have hstep : count (r - 1) ≤ count (Q - r) :=
        count_pred_le_count_sub (t := t + 1) hQ hr1 h2r
      rw [hneq]
      omega

/-- Every interval outside the two exceptional sets has at least three good partitions. -/
theorem three_le_count_of_not_exceptional (n : ℕ) (hn : 1 ≤ n) (h1 : ¬ Nu n) (h2 : ¬ E2 n) :
    3 ≤ count n := by
  have key : ∀ m : ℕ, 1 ≤ m → ¬ Nu m → ¬ E2 m → 3 ≤ count m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih => exact three_le_count_step m ih
  exact key n hn h1 h2

/-- Every member of the first exceptional set has exactly one good partition. -/
theorem count_eq_one_of_nu {n : ℕ} (h : Nu n) : count n = 1 := by
  rcases h with rfl | rfl | rfl | rfl | ⟨t, ht, hN⟩
  · exact count_eq_one_small 1 (by decide)
  · exact count_eq_one_small 2 (by decide)
  · exact count_eq_one_small 3 (by decide)
  · exact count_eq_one_small 4 (by decide)
  rcases hN with hN | hN | hN | hN | hN | hN | hN | hN
  · -- Four below a power: the family starts at twenty-seven.
    by_cases ht3 : 3 ≤ t
    · have heq : count (3 ^ 3 - 4) = count (3 ^ t - 4) :=
        count_sub_eq (by norm_num) (by norm_num) (by norm_num) ht3
      have hval : (3 : ℕ) ^ 3 - 4 = 23 := by norm_num
      have hn : n = 3 ^ t - 4 := by omega
      rw [hn, ← heq, hval]
      exact count_eq_one_small 23 (by decide)
    · have h9 : (3 : ℕ) ^ t = 9 := by
        have ht2 : t = 2 := by omega
        subst ht2
        norm_num
      have hn : n = 5 := by omega
      subst hn
      exact count_eq_one_small 5 (by decide)
  · -- Two below a power.
    have heq : count (3 ^ 2 - 2) = count (3 ^ t - 2) :=
      count_sub_eq (by norm_num) (by norm_num) (by norm_num) ht
    have hval : (3 : ℕ) ^ 2 - 2 = 7 := by norm_num
    have hn : n = 3 ^ t - 2 := by omega
    rw [hn, ← heq, hval]
    exact count_eq_one_small 7 (by decide)
  · -- One below a power.
    have heq : count (3 ^ 2 - 1) = count (3 ^ t - 1) :=
      count_sub_eq (by norm_num) (by norm_num) (by norm_num) ht
    have hval : (3 : ℕ) ^ 2 - 1 = 8 := by norm_num
    have hn : n = 3 ^ t - 1 := by omega
    rw [hn, ← heq, hval]
    exact count_eq_one_small 8 (by decide)
  · -- A power itself.
    have heq : count (3 ^ 2 + 0) = count (3 ^ t + 0) := count_add_eq (by norm_num) ht
    have hval : (3 : ℕ) ^ 2 + 0 = 9 := by norm_num
    have hn : n = 3 ^ t + 0 := by omega
    rw [hn, ← heq, hval]
    exact count_eq_one_small 9 (by decide)
  · -- One above a power.
    have heq : count (3 ^ 2 + 1) = count (3 ^ t + 1) := count_add_eq (by norm_num) ht
    have hval : (3 : ℕ) ^ 2 + 1 = 10 := by norm_num
    rw [hN, ← heq, hval]
    exact count_eq_one_small 10 (by decide)
  · -- Two above a power.
    have heq : count (3 ^ 2 + 2) = count (3 ^ t + 2) := count_add_eq (by norm_num) ht
    have hval : (3 : ℕ) ^ 2 + 2 = 11 := by norm_num
    rw [hN, ← heq, hval]
    exact count_eq_one_small 11 (by decide)
  · -- Three above a power: the family starts at twenty-seven.
    by_cases ht3 : 3 ≤ t
    · have heq : count (3 ^ 3 + 3) = count (3 ^ t + 3) := count_add_eq (by norm_num) ht3
      have hval : (3 : ℕ) ^ 3 + 3 = 30 := by norm_num
      rw [hN, ← heq, hval]
      exact count_eq_one_small 30 (by decide)
    · have h9 : (3 : ℕ) ^ t = 9 := by
        have ht2 : t = 2 := by omega
        subst ht2
        norm_num
      have hn : n = 12 := by omega
      subst hn
      exact count_eq_one_small 12 (by decide)
  · -- Five above a power: the family starts at eighty-one.
    by_cases ht4 : 4 ≤ t
    · have heq : count (3 ^ 4 + 5) = count (3 ^ t + 5) := count_add_eq (by norm_num) ht4
      have hval : (3 : ℕ) ^ 4 + 5 = 86 := by norm_num
      rw [hN, ← heq, hval]
      exact count_eq_one_small 86 (by decide)
    · have hsm : (3 : ℕ) ^ t = 9 ∨ (3 : ℕ) ^ t = 27 := by
        rcases (show t = 2 ∨ t = 3 by omega) with rfl | rfl
        · exact Or.inl (by norm_num)
        · exact Or.inr (by norm_num)
      have hn : n = 14 ∨ n = 32 := by omega
      rcases hn with rfl | rfl
      · exact count_eq_one_small 14 (by decide)
      · exact count_eq_one_small 32 (by decide)

/-- Every member of the second exceptional set has exactly two good partitions. -/
theorem count_eq_two_of_e2 {n : ℕ} (h : E2 n) : count n = 2 := by
  rcases h with rfl | ⟨t, ht, hE⟩ | ⟨t, ht, hE⟩
  · exact count_eq_two_small 13 (by decide)
  · -- Three below a power: the family starts at nine.
    have heq : count (3 ^ 2 - 3) = count (3 ^ t - 3) :=
      count_sub_eq (by norm_num) (by norm_num) (by norm_num) ht
    have hval : (3 : ℕ) ^ 2 - 3 = 6 := by norm_num
    have hn : n = 3 ^ t - 3 := by omega
    rw [hn, ← heq, hval]
    exact count_eq_two_small 6 (by decide)
  · -- Six below a power: the family starts at eighty-one.
    by_cases ht4 : 4 ≤ t
    · have heq : count (3 ^ 4 - 6) = count (3 ^ t - 6) :=
        count_sub_eq (by norm_num) (by norm_num) (by norm_num) ht4
      have hval : (3 : ℕ) ^ 4 - 6 = 75 := by norm_num
      have hn : n = 3 ^ t - 6 := by omega
      rw [hn, ← heq, hval]
      exact count_eq_two_small 75 (by decide)
    · have h27 : (3 : ℕ) ^ t = 27 := by
        have ht3 : t = 3 := by omega
        subst ht3
        norm_num
      have hn : n = 21 := by omega
      subst hn
      exact count_eq_two_small 21 (by decide)

end

end GNM

import GN.Elementary
import GN.Transfer

namespace GN
noncomputable section

/-- The interval induction, separated from its sequence-construction input. -/
theorem hasGood_all_of_critical
    (hcritical : ∀ (P r t : ℕ), P = 3^t → 2*r < P → r % 3 = 2 →
      HasGood (interval r) → HasGood (interval (P+r))) :
    ∀ n : ℕ, HasGood (interval n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using hasGood_empty
    have hnpos : 0 < n := by omega
    let t := Nat.log 3 n
    let P := 3^t
    have hP : P = 3^t := rfl
    have hPpos : 0 < P := pow_pos (by norm_num) t
    have hPle : P ≤ n := Nat.pow_log_le_self 3 hn
    have hnlt : n < 3*P := by
      have h := Nat.lt_pow_succ_log_self (b := 3) (by norm_num) n
      simpa only [Nat.succ_eq_add_one, pow_succ, mul_comm] using h
    have hPodd : P % 2 = 1 := by simp [P, Nat.pow_mod]
    by_cases hu : 3*P < 2*n
    · apply upper_pair_extension hP hu hnlt
      apply ih
      omega
    · let r := n-P
      have hnP : n = P+r := by dsimp [r]; omega
      have hPr : 2*r < P := by omega
      by_cases hc : r % 3 = 2
      · rw [hnP]
        apply hcritical P r t hP hPr hc
        apply ih
        omega
      · rw [hnP]
        apply lower_symmetric_extension hP hPr (by omega)
        apply ih
        omega

/-- The signed construction supplies every critical step above the three literal bases. -/
theorem critical_large_of_permutations
    (hperm : ∀ k : ℤ, 3 ≤ k → ∀ j : ℤ, -k ≤ j ∧ j ≤ k →
      ∃ σ : ℤ → ℤ, DisplacementPermutation k j σ)
    {P r t : ℕ} (hP : P = 3^t) (hPr : 2*r < P) (hr : 11 ≤ r)
    (hmod : r % 3 = 2) (hs : HasGood (interval r)) :
    HasGood (interval (P+r)) := by
  apply critical_extension_of_frames hP hPr hmod hs
  intro a ha har ha3
  let k : ℤ := (r:ℤ)/3
  have hrk : (r:ℤ) = 3*k+2 := by
    have hm : (r:ℤ)%3 = 2 := by exact_mod_cast hmod
    dsimp [k]
    omega
  have hk : 3 ≤ k := by omega
  rw [hrk]
  apply exists_zeroPartition_signed (by omega) ha (by omega) ha3
  intro j hj hj'
  exact hperm k hk j ⟨hj, hj'⟩

end
end GN

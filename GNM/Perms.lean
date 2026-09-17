import GNM.Distinct
import GNM.Data.Perms

/-!
# The finite permutation certificates

For every `k` between four and twenty-one and every hole `j` the tables carry three permutations of
the centered interval `[-k, k]` with the hole removed whose displacements run through the nonzero
centered interval. The certificates below state, for the positional tables read back as functions,
exactly the two image equalities that characterise a displacement permutation together with the
distinctness of the three rows at each hole; they are finite statements, checked by evaluation.
What the rest of the development uses is the last statement: three distinct displacement
permutations at every hole of every small centered interval.
-/

namespace GNM

open GN

/-- The permutation named by a row of the positional table: the entry at index `u + k`, shifted back
to the centered convention. -/
noncomputable def witnessPerm (k j : ℤ) (i : ℕ) (u : ℤ) : ℤ :=
  (permWitness k.toNat j.toNat i).getD (u + k).toNat 0 - (k + 1)

/-- The `i`-th row at every hole of the centered interval `[-k, k]` is a permutation of its domain
whose displacements are exactly the nonzero values of `[-k, k]`. -/
def PermCertificate (k : ℤ) (i : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 0 k,
    (displacementDomain k j).image (witnessPerm k j i) = displacementDomain k j ∧
      (displacementDomain k j).image (fun u => witnessPerm k j i u - u) =
        (Finset.Icc (-k) k).erase 0 ∧
      (displacementDomain k j).card ≤ ((Finset.Icc (-k) k).erase 0).card

/-- The three rows at every hole of the centered interval `[-k, k]` are pairwise distinct. -/
def DistinctCertificate (k : ℤ) : Prop :=
  ∀ j ∈ Finset.Icc 0 k,
    (∃ u ∈ displacementDomain k j, witnessPerm k j 0 u ≠ witnessPerm k j 1 u) ∧
      (∃ u ∈ displacementDomain k j, witnessPerm k j 0 u ≠ witnessPerm k j 2 u) ∧
      (∃ u ∈ displacementDomain k j, witnessPerm k j 1 u ≠ witnessPerm k j 2 u)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-4, 4]` is a displacement
permutation. -/
private theorem perm_certificate_4_0 : PermCertificate 4 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-4, 4]` is a displacement
permutation. -/
private theorem perm_certificate_4_1 : PermCertificate 4 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-4, 4]` is a displacement
permutation. -/
private theorem perm_certificate_4_2 : PermCertificate 4 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-4, 4]` are pairwise
distinct. -/
private theorem distinct_certificate_4 : DistinctCertificate 4 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-5, 5]` is a displacement
permutation. -/
private theorem perm_certificate_5_0 : PermCertificate 5 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-5, 5]` is a displacement
permutation. -/
private theorem perm_certificate_5_1 : PermCertificate 5 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-5, 5]` is a displacement
permutation. -/
private theorem perm_certificate_5_2 : PermCertificate 5 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-5, 5]` are pairwise
distinct. -/
private theorem distinct_certificate_5 : DistinctCertificate 5 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-6, 6]` is a displacement
permutation. -/
private theorem perm_certificate_6_0 : PermCertificate 6 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-6, 6]` is a displacement
permutation. -/
private theorem perm_certificate_6_1 : PermCertificate 6 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-6, 6]` is a displacement
permutation. -/
private theorem perm_certificate_6_2 : PermCertificate 6 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-6, 6]` are pairwise
distinct. -/
private theorem distinct_certificate_6 : DistinctCertificate 6 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-7, 7]` is a displacement
permutation. -/
private theorem perm_certificate_7_0 : PermCertificate 7 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-7, 7]` is a displacement
permutation. -/
private theorem perm_certificate_7_1 : PermCertificate 7 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-7, 7]` is a displacement
permutation. -/
private theorem perm_certificate_7_2 : PermCertificate 7 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-7, 7]` are pairwise
distinct. -/
private theorem distinct_certificate_7 : DistinctCertificate 7 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-8, 8]` is a displacement
permutation. -/
private theorem perm_certificate_8_0 : PermCertificate 8 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-8, 8]` is a displacement
permutation. -/
private theorem perm_certificate_8_1 : PermCertificate 8 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-8, 8]` is a displacement
permutation. -/
private theorem perm_certificate_8_2 : PermCertificate 8 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-8, 8]` are pairwise
distinct. -/
private theorem distinct_certificate_8 : DistinctCertificate 8 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-9, 9]` is a displacement
permutation. -/
private theorem perm_certificate_9_0 : PermCertificate 9 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-9, 9]` is a displacement
permutation. -/
private theorem perm_certificate_9_1 : PermCertificate 9 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-9, 9]` is a displacement
permutation. -/
private theorem perm_certificate_9_2 : PermCertificate 9 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-9, 9]` are pairwise
distinct. -/
private theorem distinct_certificate_9 : DistinctCertificate 9 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-10, 10]` is a displacement
permutation. -/
private theorem perm_certificate_10_0 : PermCertificate 10 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-10, 10]` is a displacement
permutation. -/
private theorem perm_certificate_10_1 : PermCertificate 10 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-10, 10]` is a displacement
permutation. -/
private theorem perm_certificate_10_2 : PermCertificate 10 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-10, 10]` are pairwise
distinct. -/
private theorem distinct_certificate_10 : DistinctCertificate 10 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-11, 11]` is a displacement
permutation. -/
private theorem perm_certificate_11_0 : PermCertificate 11 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-11, 11]` is a displacement
permutation. -/
private theorem perm_certificate_11_1 : PermCertificate 11 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-11, 11]` is a displacement
permutation. -/
private theorem perm_certificate_11_2 : PermCertificate 11 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-11, 11]` are pairwise
distinct. -/
private theorem distinct_certificate_11 : DistinctCertificate 11 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-12, 12]` is a displacement
permutation. -/
private theorem perm_certificate_12_0 : PermCertificate 12 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-12, 12]` is a displacement
permutation. -/
private theorem perm_certificate_12_1 : PermCertificate 12 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-12, 12]` is a displacement
permutation. -/
private theorem perm_certificate_12_2 : PermCertificate 12 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-12, 12]` are pairwise
distinct. -/
private theorem distinct_certificate_12 : DistinctCertificate 12 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-13, 13]` is a displacement
permutation. -/
private theorem perm_certificate_13_0 : PermCertificate 13 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-13, 13]` is a displacement
permutation. -/
private theorem perm_certificate_13_1 : PermCertificate 13 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-13, 13]` is a displacement
permutation. -/
private theorem perm_certificate_13_2 : PermCertificate 13 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-13, 13]` are pairwise
distinct. -/
private theorem distinct_certificate_13 : DistinctCertificate 13 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-14, 14]` is a displacement
permutation. -/
private theorem perm_certificate_14_0 : PermCertificate 14 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-14, 14]` is a displacement
permutation. -/
private theorem perm_certificate_14_1 : PermCertificate 14 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-14, 14]` is a displacement
permutation. -/
private theorem perm_certificate_14_2 : PermCertificate 14 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-14, 14]` are pairwise
distinct. -/
private theorem distinct_certificate_14 : DistinctCertificate 14 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-15, 15]` is a displacement
permutation. -/
private theorem perm_certificate_15_0 : PermCertificate 15 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-15, 15]` is a displacement
permutation. -/
private theorem perm_certificate_15_1 : PermCertificate 15 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-15, 15]` is a displacement
permutation. -/
private theorem perm_certificate_15_2 : PermCertificate 15 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-15, 15]` are pairwise
distinct. -/
private theorem distinct_certificate_15 : DistinctCertificate 15 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-16, 16]` is a displacement
permutation. -/
private theorem perm_certificate_16_0 : PermCertificate 16 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-16, 16]` is a displacement
permutation. -/
private theorem perm_certificate_16_1 : PermCertificate 16 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-16, 16]` is a displacement
permutation. -/
private theorem perm_certificate_16_2 : PermCertificate 16 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-16, 16]` are pairwise
distinct. -/
private theorem distinct_certificate_16 : DistinctCertificate 16 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-17, 17]` is a displacement
permutation. -/
private theorem perm_certificate_17_0 : PermCertificate 17 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-17, 17]` is a displacement
permutation. -/
private theorem perm_certificate_17_1 : PermCertificate 17 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-17, 17]` is a displacement
permutation. -/
private theorem perm_certificate_17_2 : PermCertificate 17 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-17, 17]` are pairwise
distinct. -/
private theorem distinct_certificate_17 : DistinctCertificate 17 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-18, 18]` is a displacement
permutation. -/
private theorem perm_certificate_18_0 : PermCertificate 18 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-18, 18]` is a displacement
permutation. -/
private theorem perm_certificate_18_1 : PermCertificate 18 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-18, 18]` is a displacement
permutation. -/
private theorem perm_certificate_18_2 : PermCertificate 18 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-18, 18]` are pairwise
distinct. -/
private theorem distinct_certificate_18 : DistinctCertificate 18 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-19, 19]` is a displacement
permutation. -/
private theorem perm_certificate_19_0 : PermCertificate 19 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-19, 19]` is a displacement
permutation. -/
private theorem perm_certificate_19_1 : PermCertificate 19 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-19, 19]` is a displacement
permutation. -/
private theorem perm_certificate_19_2 : PermCertificate 19 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-19, 19]` are pairwise
distinct. -/
private theorem distinct_certificate_19 : DistinctCertificate 19 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-20, 20]` is a displacement
permutation. -/
private theorem perm_certificate_20_0 : PermCertificate 20 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-20, 20]` is a displacement
permutation. -/
private theorem perm_certificate_20_1 : PermCertificate 20 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-20, 20]` is a displacement
permutation. -/
private theorem perm_certificate_20_2 : PermCertificate 20 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-20, 20]` are pairwise
distinct. -/
private theorem distinct_certificate_20 : DistinctCertificate 20 := by
  unfold DistinctCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first row at every hole of the centered interval `[-21, 21]` is a displacement
permutation. -/
private theorem perm_certificate_21_0 : PermCertificate 21 0 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second row at every hole of the centered interval `[-21, 21]` is a displacement
permutation. -/
private theorem perm_certificate_21_1 : PermCertificate 21 1 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third row at every hole of the centered interval `[-21, 21]` is a displacement
permutation. -/
private theorem perm_certificate_21_2 : PermCertificate 21 2 := by
  unfold PermCertificate
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three rows at every hole of the centered interval `[-21, 21]` are pairwise
distinct. -/
private theorem distinct_certificate_21 : DistinctCertificate 21 := by
  unfold DistinctCertificate
  decide

/-- The four finite certificates, at every `k` from four to twenty-one. -/
private theorem certificates_of_le_21 {k : ℤ} (hk : 4 ≤ k) (hk' : k ≤ 21) :
    PermCertificate k 0 ∧ PermCertificate k 1 ∧ PermCertificate k 2 ∧
      DistinctCertificate k := by
  interval_cases k
  · exact ⟨perm_certificate_4_0, perm_certificate_4_1, perm_certificate_4_2,
      distinct_certificate_4⟩
  · exact ⟨perm_certificate_5_0, perm_certificate_5_1, perm_certificate_5_2,
      distinct_certificate_5⟩
  · exact ⟨perm_certificate_6_0, perm_certificate_6_1, perm_certificate_6_2,
      distinct_certificate_6⟩
  · exact ⟨perm_certificate_7_0, perm_certificate_7_1, perm_certificate_7_2,
      distinct_certificate_7⟩
  · exact ⟨perm_certificate_8_0, perm_certificate_8_1, perm_certificate_8_2,
      distinct_certificate_8⟩
  · exact ⟨perm_certificate_9_0, perm_certificate_9_1, perm_certificate_9_2,
      distinct_certificate_9⟩
  · exact ⟨perm_certificate_10_0, perm_certificate_10_1, perm_certificate_10_2,
      distinct_certificate_10⟩
  · exact ⟨perm_certificate_11_0, perm_certificate_11_1, perm_certificate_11_2,
      distinct_certificate_11⟩
  · exact ⟨perm_certificate_12_0, perm_certificate_12_1, perm_certificate_12_2,
      distinct_certificate_12⟩
  · exact ⟨perm_certificate_13_0, perm_certificate_13_1, perm_certificate_13_2,
      distinct_certificate_13⟩
  · exact ⟨perm_certificate_14_0, perm_certificate_14_1, perm_certificate_14_2,
      distinct_certificate_14⟩
  · exact ⟨perm_certificate_15_0, perm_certificate_15_1, perm_certificate_15_2,
      distinct_certificate_15⟩
  · exact ⟨perm_certificate_16_0, perm_certificate_16_1, perm_certificate_16_2,
      distinct_certificate_16⟩
  · exact ⟨perm_certificate_17_0, perm_certificate_17_1, perm_certificate_17_2,
      distinct_certificate_17⟩
  · exact ⟨perm_certificate_18_0, perm_certificate_18_1, perm_certificate_18_2,
      distinct_certificate_18⟩
  · exact ⟨perm_certificate_19_0, perm_certificate_19_1, perm_certificate_19_2,
      distinct_certificate_19⟩
  · exact ⟨perm_certificate_20_0, perm_certificate_20_1, perm_certificate_20_2,
      distinct_certificate_20⟩
  · exact ⟨perm_certificate_21_0, perm_certificate_21_1, perm_certificate_21_2,
      distinct_certificate_21⟩

/-- Three distinct displacement permutations at every hole, for every `k` from four to
twenty-one. -/
theorem threeDisp_of_le_21 {k j : ℤ} (hk : 4 ≤ k) (hk' : k ≤ 21) (hj : -k ≤ j ∧ j ≤ k) :
    ThreeDisp k j := by
  obtain ⟨hp0, hp1, hp2, hd⟩ := certificates_of_le_21 hk hk'
  have main : ∀ m : ℤ, 0 ≤ m → m ≤ k → ThreeDisp k m := by
    intro m hm0 hmk
    have hmem : m ∈ Finset.Icc (0 : ℤ) k := Finset.mem_Icc.mpr ⟨hm0, hmk⟩
    obtain ⟨e0, d0, c0⟩ := hp0 m hmem
    obtain ⟨e1, d1, c1⟩ := hp1 m hmem
    obtain ⟨e2, d2, c2⟩ := hp2 m hmem
    obtain ⟨n01, n02, n12⟩ := hd m hmem
    exact ⟨witnessPerm k m 0, witnessPerm k m 1, witnessPerm k m 2,
      (displacementPermutation_iff k m _).mp (displacementPermutation_of_images e0 d0 c0),
      (displacementPermutation_iff k m _).mp (displacementPermutation_of_images e1 d1 c1),
      (displacementPermutation_iff k m _).mp (displacementPermutation_of_images e2 d2 c2),
      n01, n02, n12⟩
  rcases le_or_gt 0 j with h | h
  · exact main j h hj.2
  · have hneg := ThreeDisp.neg (main (-j) (by omega) (by omega))
    rwa [neg_neg] at hneg

end GNM

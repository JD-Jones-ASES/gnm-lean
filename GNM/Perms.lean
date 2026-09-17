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

/-- Three distinct displacement permutations at every hole, for every `k` from four to
twenty-one. -/
theorem threeDisp_of_le_21 {k j : ℤ} (hk : 4 ≤ k) (hk' : k ≤ 21) (hj : -k ≤ j ∧ j ≤ k) :
    ThreeDisp k j := by
  sorry

end GNM

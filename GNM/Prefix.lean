import GNM.Perms

/-!
# Prefix amplification

The gluing theorem of the underlying development fills the small displacements of a permutation with
one fixed prefix, the doubling permutation of an initial interval. Nothing about the prefix is used
beyond its being a permutation of that interval with the small displacements, so an arbitrary prefix
may be glued in its place, and the glued permutation agrees with the prefix on the prefix positions.
Three distinct prefixes therefore give three distinct permutations with the same displacement set,
and a strong induction on the length of the interval turns three permutations at small sizes into
three permutations at every size and every hole.
-/

namespace GNM

open GN

noncomputable section

/-- Gluing with an arbitrary prefix: any permutation of the initial interval with the small
displacements extends a pairing to a permutation of the positional interval with a prescribed hole,
and the extension agrees with the prefix on the prefix positions. -/
theorem with_prefix {d k h : ℤ} {ps : Finset (ℤ × ℤ)} (hl : LangfordPairing d k h ps) {τ : ℤ → ℤ}
    (hτ : PermutationWithDifferences (Finset.Icc 1 (2 * (d - 1)))
      ((Finset.Icc (-(d - 1)) (d - 1)).erase 0) τ) :
    ∃ σ : ℤ → ℤ, PermutationWithDifferences ((Finset.Icc 1 (2 * k + 1)).erase (h + 2 * (d - 1)))
        ((Finset.Icc (-k) k).erase 0) σ ∧
      ∀ x ∈ Finset.Icc 1 (2 * (d - 1)), σ x = τ x := by
  sorry

/-- Three distinct prefixes glued to one pairing give three distinct permutations. -/
theorem threeA_of_pairing {d k h : ℤ} {ps : Finset (ℤ × ℤ)} (hl : LangfordPairing d k h ps)
    (hM : ThreeM (d - 1)) : ThreeA k (h + 2 * (d - 1)) := by
  sorry

/-- The upper-half holes with a variable prefix: the six explicit pairing families of the underlying
development, with the prefix half-length `d − 1` or `d − 3` for `d = (k + 2) / 3 ≥ 8`. -/
theorem threeA_high {k H : ℤ} (hk : 22 ≤ k) (hH : k + 1 ≤ H ∧ H ≤ 2 * k + 1)
    (hM : ∀ q : ℤ, 5 ≤ q → q < k → ThreeM q) : ThreeA k H := by
  sorry

/-- Reflecting the positions moves the hole `H` to `2k + 2 − H`. -/
theorem threeA_reflect {k H : ℤ} (hk : 0 ≤ k) (h : ThreeA k H) : ThreeA k (2 * k + 2 - H) := by
  sorry

/-- Three permutations of `[1, 2q]` with displacements `±1, …, ±q`, for every `q ≥ 5`. -/
theorem threeM_all (q : ℤ) (hq : 5 ≤ q) : ThreeM q := by
  sorry

/-- Three permutations of `[1, 2k + 1]` with any one position removed, for every `k ≥ 4`. -/
theorem threeA_all {k H : ℤ} (hk : 4 ≤ k) (hH : 1 ≤ H ∧ H ≤ 2 * k + 1) : ThreeA k H := by
  sorry

/-- Three displacement permutations at every hole of the centered interval, for every `k ≥ 4`. -/
theorem threeDisp_all {k j : ℤ} (hk : 4 ≤ k) (hj : -k ≤ j ∧ j ≤ k) : ThreeDisp k j := by
  sorry

end

end GNM

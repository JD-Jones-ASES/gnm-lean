import GNM.Lift

/-!
# The negative offsets

An interval `{1, …, Q − r}` just below a power of three is partitioned by taking a good partition of
`{1, …, r − 1}` and completing it with the canonical pairs `{d, Q − d}`, `r ≤ d ≤ (Q − 1)/2`; the
source is recovered from the target as the blocks lying below `r`, so distinct sources give distinct
targets and the count at `r − 1` is a lower bound for the count at `Q − r`. When `r − 1` is itself
exceptional that route is closed, and two gadgets take its place: one for the offsets just below a
power, where a single canonical pair is merged with the element `Q − R`, and one for the offsets
just above a power, where three pairs are merged.
-/

namespace GNM

open GN

noncomputable section

/-- The negative target: a partition of `{1, …, r − 1}` and the canonical pairs above `r`. -/
def targetC (Q r : ℤ) (src : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  src ∪ canonicalPairs Q r ((Q - 1) / 2)

/-- The negative target is a good partition of `{1, …, Q − r}`. -/
theorem targetC_goodOn {Q r t : ℕ} (hQ : Q = 3 ^ t) (hr : 1 ≤ r) (hQr : 2 * r < Q)
    {src : Finset (Finset ℤ)} (hsrc : GoodOn (interval (r - 1)) src) :
    GoodOn (interval (Q - r)) (targetC (Q : ℤ) (r : ℤ) src) := by
  sorry

/-- The source can be read back off the negative target: it is the set of blocks below `r`. -/
theorem targetC_src {Q r t : ℕ} (hQ : Q = 3 ^ t) (hr : 1 ≤ r) (hQr : 2 * r < Q)
    {src : Finset (Finset ℤ)} (hsrc : GoodOn (interval (r - 1)) src) :
    (targetC (Q : ℤ) (r : ℤ) src).filter (fun b => ∀ x ∈ b, x < (r : ℤ)) = src := by
  sorry

/-- The count at `r − 1` bounds the count at `Q − r`. -/
theorem count_pred_le_count_sub {Q r t : ℕ} (hQ : Q = 3 ^ t) (hr : 1 ≤ r) (hQr : 2 * r < Q) :
    count (r - 1) ≤ count (Q - r) := by
  sorry

/-- The first gadget: for an offset `R − e + 1` just below a power `R`, the canonical completion and
the two single merges of a canonical pair with the element `Q − R` give three good partitions. -/
theorem three_le_count_sub_below {Q R e t s : ℕ} (hR : R = 3 ^ s) (hs : 3 ≤ s)
    (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) (hQ : Q = 3 ^ t) (hQR : 3 * R ≤ Q) :
    3 ≤ count (Q - (R - e + 1)) := by
  sorry

/-- The second gadget: for an offset `R + δ` just above a power `R`, an explicit source at `R + δ −
1` and the three-pair merge at two different starting deficits give three good partitions. -/
theorem three_le_count_sub_above {Q R δ t s : ℕ} (hR : R = 3 ^ s) (hs : 4 ≤ s)
    (hδ : δ = 1 ∨ δ = 2 ∨ δ = 3 ∨ δ = 4 ∨ δ = 6) (hQ : Q = 3 ^ t) (hQR : 3 * R ≤ Q) :
    3 ≤ count (Q - (R + δ)) := by
  sorry

end

end GNM

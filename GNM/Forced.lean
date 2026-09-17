import GNM.Basic

/-!
# Forced blocks and forced deficits

Above the halfway point of a power of three the shape of a block is forced: a block containing a
large element sums to the power (or, just above the power, either to the power with one large
element or to three times the power with three large elements), and its remaining elements are
small. Counting the mass of the small elements against the deficits they have to supply then forces
every large deficit to be canonical, that is, to be one of the pairs `{d, Q − d}`. These are the two
facts the truncation of the lift rests on, and with them the counts are constant along each family
of powers.
-/

namespace GNM

open GN

noncomputable section

/-- Negative offsets: a block containing an element above the halfway point sums to the power, and
its other elements lie below the halfway point. -/
theorem high_block_sub {Q r t : ℕ} (hQ : Q = 3 ^ t) (hQr : 2 * r < Q) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (Q - r)) bs) {b : Finset ℤ} (hb : b ∈ bs) {x : ℤ} (hx : x ∈ b)
    (hhigh : ((Q : ℤ) - 1) / 2 < x) :
    b.sum id = Q ∧ ∀ y ∈ b, y ≠ x → y ≤ ((Q : ℤ) - 1) / 2 := by
  sorry

/-- Positive offsets above the threshold `r(r + 1)`: a block meeting the upper half is the singleton
of the power, or sums to the power with exactly one high element, or sums to three times the power
with all three elements high. -/
theorem high_block_add {P r t : ℕ} (hP : P = 3 ^ t) (hPr : r * (r + 1) < P)
    {bs : Finset (Finset ℤ)} (hbs : GoodOn (interval (P + r)) bs) {b : Finset ℤ} (hb : b ∈ bs)
    {x : ℤ} (hx : x ∈ b) (hhigh : ((P : ℤ) - 1) / 2 < x) :
    b = {(P : ℤ)} ∨ (b.sum id = P ∧ ∀ y ∈ b, y ≠ x → y ≤ ((P : ℤ) - 1) / 2) ∨
      (b.sum id = 3 * P ∧ ∀ y ∈ b, ((P : ℤ) - 1) / 2 < y) := by
  sorry

/-- Negative offsets: every deficit above `r(r − 1)/2` is canonical. -/
theorem canonical_sub {Q r t : ℕ} (hQ : Q = 3 ^ t) (hr : 1 ≤ r) (hQr : 2 * r < Q)
    {bs : Finset (Finset ℤ)} (hbs : GoodOn (interval (Q - r)) bs) {d : ℤ}
    (hd : (r : ℤ) * (r - 1) / 2 < d) (hdr : (r : ℤ) ≤ d) (hd' : 2 * d < Q) :
    ({d, (Q : ℤ) - d} : Finset ℤ) ∈ bs := by
  sorry

/-- Positive offsets: every deficit above `r(r + 1)/2` is canonical. -/
theorem canonical_add {P r t : ℕ} (hP : P = 3 ^ t) (hPr : r * (r + 1) < P)
    {bs : Finset (Finset ℤ)} (hbs : GoodOn (interval (P + r)) bs) {d : ℤ}
    (hd : (r : ℤ) * (r + 1) / 2 < d) (hd1 : 1 ≤ d) (hd' : 2 * d < P) :
    ({d, (P : ℤ) - d} : Finset ℤ) ∈ bs := by
  sorry

end

end GNM

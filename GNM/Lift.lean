import GNM.Forced

/-!
# The lift between two powers and its inverse

Along one family of offsets the good partitions of `{1, …, Q − r}` and of `{1, …, Q' − r}`
correspond to each other: relabel every element above the halfway point of `Q` by the gap `Q' − Q`
and insert the canonical pairs `{d, Q' − d}` for the deficits in between. The inverse operation
drops those pairs and relabels back, and it is inverse precisely because above the threshold every
large deficit is forced to be canonical, so the pairs to drop are present in every good partition of
the larger interval. The same pair of maps works at the positive offsets, with the threshold `r(r +
1)`.
-/

namespace GNM

open GN

noncomputable section

/-- The canonical pairs `{d, Q − d}` for the deficits `d` in a range. -/
def canonicalPairs (Q lo hi : ℤ) : Finset (Finset ℤ) :=
  (Finset.Icc lo hi).image (fun d => {d, Q - d})

/-- The canonical pairs of a range partition the range and its complement. -/
theorem canonicalPairs_goodOn {Q t : ℕ} {lo hi : ℤ} (hQ : Q = 3 ^ t) (hlo : 1 ≤ lo)
    (hhi : 2 * hi < (Q : ℤ)) :
    GoodOn (Finset.Icc lo hi ∪ Finset.Icc ((Q : ℤ) - hi) ((Q : ℤ) - lo))
      (canonicalPairs (Q : ℤ) lo hi) := by
  have hQ' : (Q : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hQ
  have hgood : ∀ d ∈ Finset.Icc lo hi, GoodBlock ({d, (Q : ℤ) - d} : Finset ℤ) := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    exact goodBlock_pair (by omega) (k := t) (by rw [← hQ']; ring)
  have hdisj : ∀ d ∈ Finset.Icc lo hi, ∀ e ∈ Finset.Icc lo hi, d ≠ e →
      Disjoint ({d, (Q : ℤ) - d} : Finset ℤ) ({e, (Q : ℤ) - e} : Finset ℤ) := by
    intro d hd e he hde
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    obtain ⟨he1, he2⟩ := Finset.mem_Icc.mp he
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    omega
  have himg := goodOn_image (Finset.Icc lo hi) (fun d => ({d, (Q : ℤ) - d} : Finset ℤ)) hgood hdisj
  have hset : (Finset.Icc lo hi).biUnion (fun d => ({d, (Q : ℤ) - d} : Finset ℤ)) =
      Finset.Icc lo hi ∪ Finset.Icc ((Q : ℤ) - hi) ((Q : ℤ) - lo) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
      Finset.mem_Icc]
    constructor
    · rintro ⟨d, hd, hx | hx⟩ <;> omega
    · intro hx
      rcases hx with hx | hx
      · exact ⟨x, by omega, Or.inl rfl⟩
      · exact ⟨(Q : ℤ) - x, by omega, Or.inr (by omega)⟩
  rw [hset] at himg
  exact himg

/-- The lift from `Q` to `Q'`: relabel every element above the halfway point of `Q` by the gap, and
add the canonical pairs for the deficits in between. -/
def liftBlocks (Q Q' : ℤ) (bs : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  bs.image (fun b => b.image (fun x => if (Q - 1) / 2 < x then x + (Q' - Q) else x)) ∪
    canonicalPairs Q' ((Q + 1) / 2) ((Q' - 1) / 2)

/-- The lift carries good partitions at a negative offset to good partitions at the same offset of
the larger power. -/
theorem liftBlocks_goodOn_sub {Q Q' r t t' : ℕ} (hQ : Q = 3 ^ t) (hQ' : Q' = 3 ^ t')
    (hle : Q ≤ Q') (hr : 1 ≤ r) (hQr : 2 * r < Q) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (Q - r)) bs) :
    GoodOn (interval (Q' - r)) (liftBlocks (Q : ℤ) (Q' : ℤ) bs) := by
  sorry

/-- The lift carries good partitions at a positive offset to good partitions at the same offset of
the larger power. -/
theorem liftBlocks_goodOn_add {P P' r t t' : ℕ} (hP : P = 3 ^ t) (hP' : P' = 3 ^ t')
    (hle : P ≤ P') (hPr : r * (r + 1) < P) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (P + r)) bs) :
    GoodOn (interval (P' + r)) (liftBlocks (P : ℤ) (P' : ℤ) bs) := by
  sorry

/-- The truncation: drop the canonical pairs for the deficits between the two halfway points and
relabel back. -/
def truncBlocks (Q Q' : ℤ) (bs : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  (bs \ canonicalPairs Q' ((Q + 1) / 2) ((Q' - 1) / 2)).image
    (fun b => b.image (fun x => if (Q' - 1) / 2 < x then x - (Q' - Q) else x))

/-- The truncation undoes the lift at a negative offset. -/
theorem truncBlocks_liftBlocks_sub {Q Q' r t t' : ℕ} (hQ : Q = 3 ^ t) (hQ' : Q' = 3 ^ t')
    (hle : Q ≤ Q') (hr : 1 ≤ r) (hQr : 2 * r < Q) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (Q - r)) bs) :
    truncBlocks (Q : ℤ) (Q' : ℤ) (liftBlocks (Q : ℤ) (Q' : ℤ) bs) = bs := by
  sorry

/-- The truncation undoes the lift at a positive offset. -/
theorem truncBlocks_liftBlocks_add {P P' r t t' : ℕ} (hP : P = 3 ^ t) (hP' : P' = 3 ^ t')
    (hle : P ≤ P') (hPr : r * (r + 1) < P) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (P + r)) bs) :
    truncBlocks (P : ℤ) (P' : ℤ) (liftBlocks (P : ℤ) (P' : ℤ) bs) = bs := by
  sorry

/-- Above the threshold the lift undoes the truncation at a negative offset, and the truncation of a
good partition is a good partition of the smaller interval. -/
theorem liftBlocks_truncBlocks_sub {Q Q' r t t' : ℕ} (hQ : Q = 3 ^ t) (hQ' : Q' = 3 ^ t')
    (hle : Q ≤ Q') (hr : 1 ≤ r) (hQr : 2 * r < Q) (hthr : r * (r - 1) < Q)
    {bs : Finset (Finset ℤ)} (hbs : GoodOn (interval (Q' - r)) bs) :
    liftBlocks (Q : ℤ) (Q' : ℤ) (truncBlocks (Q : ℤ) (Q' : ℤ) bs) = bs ∧
      GoodOn (interval (Q - r)) (truncBlocks (Q : ℤ) (Q' : ℤ) bs) := by
  sorry

/-- Above the threshold the lift undoes the truncation at a positive offset, and the truncation of a
good partition is a good partition of the smaller interval. -/
theorem liftBlocks_truncBlocks_add {P P' r t t' : ℕ} (hP : P = 3 ^ t) (hP' : P' = 3 ^ t')
    (hle : P ≤ P') (hthr : r * (r + 1) < P) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (P' + r)) bs) :
    liftBlocks (P : ℤ) (P' : ℤ) (truncBlocks (P : ℤ) (P' : ℤ) bs) = bs ∧
      GoodOn (interval (P + r)) (truncBlocks (P : ℤ) (P' : ℤ) bs) := by
  sorry

/-- The counts at a negative offset are monotone along the powers. -/
theorem count_sub_le_count_sub {r t t' : ℕ} (hr : 1 ≤ r) (h2 : 2 * r < 3 ^ t) (htt' : t ≤ t') :
    count (3 ^ t - r) ≤ count (3 ^ t' - r) := by
  sorry

end

end GNM

import GNM.Frames

/-!
# The positive offsets

An interval `{1, …, P + r}` just above a power of three is partitioned in two ways, both of which
keep a frame of triples that sum to `3P` around the power and read the rest off a smaller interval.
In the symmetric construction the frame lives on a centered interval and the smaller interval is
`{1, …, P − r − 1}`; in the signed construction the smaller interval is `{1, …, r}`, one of its
blocks is contracted at the partner, and the frame lives on the signed vertex set of the partner. In
both, the blocks summing to `3P` are exactly the frame, so the frame can be read back off the target
and three distinct frames give three distinct partitions.
-/

namespace GNM

open GN

noncomputable section

/-- Translating every block of a family by `P`. -/
def shiftBlocks (P : ℤ) (zs : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  zs.image (fun b => b.image (fun x => P + x))

/-- Translating the blocks of a family is injective in the family. -/
theorem shiftBlocks_injective (P : ℤ) : Function.Injective (shiftBlocks P) := by
  have hb : ∀ b : Finset ℤ, (b.image (fun x => P + x)).image (fun x => -P + x) = b := by
    intro b
    rw [Finset.image_image]
    have hfun : ((fun x : ℤ => -P + x) ∘ (fun x : ℤ => P + x)) = (fun x : ℤ => x) := by
      funext x
      simp only [Function.comp_apply]
      omega
    rw [hfun, Finset.image_id']
  have key : ∀ xs : Finset (Finset ℤ),
      (shiftBlocks P xs).image (fun b => b.image (fun x => -P + x)) = xs := by
    intro xs
    calc (shiftBlocks P xs).image (fun b => b.image (fun x => -P + x))
        = xs.image ((fun b : Finset ℤ => b.image (fun x : ℤ => -P + x)) ∘
            (fun b : Finset ℤ => b.image (fun x : ℤ => P + x))) := by
          simp only [shiftBlocks, Finset.image_image]
      _ = xs.image (fun b => b) := by
          refine Finset.image_congr ?_
          intro b _
          exact hb b
      _ = xs := Finset.image_id'
  intro zs ws h
  have h1 := key zs
  have h2 := key ws
  rw [h] at h1
  exact h1.symm.trans h2

/-- A translated zero-sum triple sums to three times the translation. -/
theorem sum_shift_of_zero {P : ℤ} {b : Finset ℤ} (h3 : b.card = 3) (hs : b.sum id = 0) :
    (b.image (fun x => P + x)).sum id = 3 * P := by
  have hinj : ∀ x ∈ b, ∀ y ∈ b, P + x = P + y → x = y := fun x _ y _ hxy => by omega
  rw [Finset.sum_image hinj]
  simp only [id_eq]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, h3]
  have hs' : ∑ x ∈ b, (x : ℤ) = 0 := hs
  rw [hs']
  push_cast
  ring

/-- The symmetric target: a partition of `{1, …, P − r − 1}`, the frame translated to the power, and
the singleton of the power itself when three divides the offset. -/
def targetA (P : ℤ) (src zs : Finset (Finset ℤ)) (central : Bool) : Finset (Finset ℤ) :=
  src ∪ shiftBlocks P zs ∪ (if central then {{P}} else ∅)

/-- The symmetric target is a good partition of `{1, …, P + r}`. -/
theorem targetA_goodOn {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) {src zs : Finset (Finset ℤ)}
    (hsrc : GoodOn (interval (P - r - 1)) src) (hz : ZeroPartition (frameSet r) zs) :
    GoodOn (interval (P + r)) (targetA (P : ℤ) src zs (decide (r % 3 = 0))) := by
  sorry

/-- The frame can be read back off the symmetric target: it is the set of blocks summing to `3P`. -/
theorem targetA_frame {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) {src zs : Finset (Finset ℤ)} {c : Bool}
    (hsrc : GoodOn (interval (P - r - 1)) src) (hz : ZeroPartition (frameSet r) zs) :
    (targetA (P : ℤ) src zs c).filter (fun b => b.sum id = 3 * (P : ℤ)) =
      shiftBlocks (P : ℤ) zs := by
  sorry

/-- The source can be read back off the symmetric target: it is the set of blocks inside `{1, …, P −
r − 1}`. -/
theorem targetA_src {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) {src zs : Finset (Finset ℤ)} {c : Bool}
    (hsrc : GoodOn (interval (P - r - 1)) src) (hz : ZeroPartition (frameSet r) zs) :
    (targetA (P : ℤ) src zs c).filter (fun b => ∀ x ∈ b, x ≤ (P : ℤ) - r - 1) = src := by
  sorry

/-- Three symmetric frames at an offset congruent to zero or one modulo three give three good
partitions of `{1, …, P + r}`. -/
theorem three_le_count_add_of_threeFrameA {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) (hZ : ThreeFrameA r) : 3 ≤ count (P + r) := by
  sorry

/-- Offset four: three explicit good partitions of `{1, …, P + 4}` for every power at least
twenty-seven. -/
theorem three_le_count_add_four {P t : ℕ} (hP : P = 3 ^ t) (ht : 3 ≤ t) : 3 ≤ count (P + 4) := by
  sorry

/-- Offset six: the two good partitions of `{1, …, 6}` extended by complement pairs, with the
symmetric frame at `k = 2` and its negation. -/
theorem three_le_count_add_six {P t : ℕ} (hP : P = 3 ^ t) (ht : 3 ≤ t) : 3 ≤ count (P + 6) := by
  sorry

/-- The contracted source of the signed construction: the source partition with the block through
the largest element contracted at the partner, and the resulting pair removed when it collides with
a complement pair. -/
def contractedSource (P r a : ℤ) (bs : Finset (Finset ℤ)) (b : Finset ℤ) : Finset (Finset ℤ) :=
  if P - (r + a) ∈ criticalSupport r a then
    (insert (contractBlock b a r) (bs.erase b)).erase {r + a, P - (r + a)}
  else insert (contractBlock b a r) (bs.erase b)

/-- The elements below the power that neither the contracted source nor the translated frame covers.
-/
def uncovered (P r a : ℤ) (L : Finset (Finset ℤ)) : Finset ℤ :=
  Finset.Icc 1 (P - 1) \ (L.biUnion id ∪ (signedVertices r a).image (fun x => P + x))

/-- The signed target: the contracted source, the translated signed frame, the singleton of the
power, and the complement pairs `{x, P − x}` over the elements still uncovered. -/
def targetB (P r a : ℤ) (bs : Finset (Finset ℤ)) (b : Finset ℤ) (zs : Finset (Finset ℤ)) :
    Finset (Finset ℤ) :=
  contractedSource P r a bs b ∪ shiftBlocks P zs ∪ {{P}} ∪
    ((uncovered P r a (contractedSource P r a bs b)).filter (fun x => 2 * x < P)).image
      (fun x => {x, P - x})

/-- The signed target is a good partition of `{1, …, P + r}`. -/
theorem targetB_goodOn {P r t : ℕ} {a : ℤ} {bs zs : Finset (Finset ℤ)} {b : Finset ℤ}
    (hP : P = 3 ^ t) (hPr : 2 * r < P) (hs : GoodOn (interval r) bs) (hb : b ∈ bs) (ha : a ∈ b)
    (hr : (r : ℤ) ∈ b) (har : a ≠ (r : ℤ))
    (hz : ZeroPartition (signedVertices (r : ℤ) a) zs) :
    GoodOn (interval (P + r)) (targetB (P : ℤ) (r : ℤ) a bs b zs) := by
  sorry

/-- The frame can be read back off the signed target: it is the set of blocks summing to `3P`. -/
theorem targetB_frame {P r t : ℕ} {a : ℤ} {bs zs : Finset (Finset ℤ)} {b : Finset ℤ}
    (hP : P = 3 ^ t) (hPr : 2 * r < P) (hs : GoodOn (interval r) bs) (hb : b ∈ bs) (ha : a ∈ b)
    (hr : (r : ℤ) ∈ b) (har : a ≠ (r : ℤ))
    (hz : ZeroPartition (signedVertices (r : ℤ) a) zs) :
    (targetB (P : ℤ) (r : ℤ) a bs b zs).filter (fun c => c.sum id = 3 * (P : ℤ)) =
      shiftBlocks (P : ℤ) zs := by
  sorry

/-- The critical residue class: three signed frames give three good partitions of `{1, …, P + r}`
for every offset at least eleven congruent to two modulo three. -/
theorem three_le_count_add_of_threeFrames {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hr : 11 ≤ r) (hmod : r % 3 = 2) : 3 ≤ count (P + r) := by
  sorry

/-- Offset eight: the unique good partition of `{1, …, 8}` has partner one, and the signed vertex
set of that partner carries three frames. -/
theorem three_le_count_add_eight {P t : ℕ} (hP : P = 3 ^ t) (ht : 3 ≤ t) : 3 ≤ count (P + 8) := by
  sorry

end

end GNM

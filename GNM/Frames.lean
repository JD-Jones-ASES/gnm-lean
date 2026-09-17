import GNM.Prefix
import GNM.Witness
import GNM.Data.Frames

/-!
# Signed frames and symmetric frames

Two supplies of three pairwise distinct frames feed the lower bounds. The first is signed: the
residue triples of a displacement permutation, together with one outer triple, partition the signed
vertex set of an offset into zero-sum triples, and the construction is injective in the permutation,
because the triple of a domain point is the only one carrying its residue-one entry. Three
displacement permutations therefore give three frames, which covers every offset congruent to two
modulo three. The second is symmetric: the two explicit triple families partition the centered
interval with its centre removed, and three pairwise distinct partitions come from that family, its
reflection, and one of three trades, which covers the offsets congruent to zero and one.
-/

namespace GNM

open GN

noncomputable section

/-- A triple of distinct integers summing to zero has three elements and sum zero. -/
private theorem card_sum_triple {x y z : ℤ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs : x + y + z = 0) :
    ({x, y, z} : Finset ℤ).card = 3 ∧ ({x, y, z} : Finset ℤ).sum id = 0 := by
  have h1 : x ∉ ({y, z} : Finset ℤ) := by simp [hxy, hxz]
  have h2 : y ∉ ({z} : Finset ℤ) := by simp [hyz]
  refine ⟨?_, ?_⟩
  · rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  · rw [Finset.sum_insert h1, Finset.sum_insert h2]
    simpa only [Finset.sum_singleton, id_eq, add_assoc] using hs

/-- The signed frame of a displacement permutation: its residue triples together with the outer
triple carrying the partner. -/
def signedFrame (k j a : ℤ) (σ : ℤ → ℤ) : Finset (Finset ℤ) :=
  (displacementDomain k j).image (residueTriple σ) ∪ {{a, 3 * k + 2, -(3 * k + 2 + a)}}

/-- The signed frame partitions the signed vertex set of the offset `3k + 2` with partner `a` into
zero-sum triples. -/
theorem signedFrame_zeroPartition {k j a : ℤ} {σ : ℤ → ℤ} (hk : 0 ≤ k) (ha : 1 ≤ a)
    (ha' : a ≤ 3 * k + 1) (haj : a = 3 * j + 1 ∨ a = -(3 * j + 1))
    (hσ : DisplacementPermutation k j σ) :
    ZeroPartition (signedVertices (3 * k + 2) a) (signedFrame k j a σ) := by
  sorry

/-- Two displacement permutations that differ at a point of their domain give different frames: the
triple of that point carries the only residue-one entry it could carry. -/
theorem signedFrame_ne {k j a : ℤ} {σ σ' : ℤ → ℤ} (hσ : DisplacementPermutation k j σ)
    (hσ' : DisplacementPermutation k j σ') {u : ℤ} (hu : u ∈ displacementDomain k j)
    (hne : σ u ≠ σ' u) : signedFrame k j a σ ≠ signedFrame k j a σ' := by
  sorry

/-- Three displacement permutations give three distinct signed frames. -/
theorem threeFrames_of_threeDisp {k j a : ℤ} (hk : 0 ≤ k) (ha : 1 ≤ a) (ha' : a ≤ 3 * k + 1)
    (haj : a = 3 * j + 1 ∨ a = -(3 * j + 1)) (h : ThreeDisp k j) : ThreeFrames (3 * k + 2) a := by
  sorry

/-- Three signed frames at offset eleven for every partner not divisible by three. -/
theorem threeFrames_eleven {a : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 10) (ha3 : ¬ (3 : ℤ) ∣ a) :
    ThreeFrames 11 a := by
  sorry

/-- Three signed frames at offset eight with partner one. -/
theorem threeFrames_eight_one : ThreeFrames 8 1 := by
  sorry

/-- Three signed frames at every offset congruent to two modulo three from eleven on, for every
partner not divisible by three. -/
theorem threeFrames_of_mod {r a : ℤ} (hr : 11 ≤ r) (hmod : r % 3 = 2) (ha : 1 ≤ a) (ha' : a < r)
    (ha3 : ¬ (3 : ℤ) ∣ a) : ThreeFrames r a := by
  sorry

/-- The centered interval `[-3k, 3k]` with its centre removed. -/
def symInterval (k : ℤ) : Finset ℤ := (Finset.Icc (-(3 * k)) (3 * k)).erase 0

/-- The symmetric family: the two explicit triple families of the underlying development, read at
the centre zero. -/
def symFamily (k : ℤ) : Finset (Finset ℤ) :=
  (Finset.Ico 0 k).image (symmA 0 k) ∪ (Finset.Ico 0 k).image (symmB 0 k)

/-- The symmetric family partitions the centered interval with its centre removed into zero-sum
triples. -/
theorem symFamily_zeroPartition (k : ℤ) (hk : 0 ≤ k) :
    ZeroPartition (symInterval k) (symFamily k) := by
  have hA : ∀ i ∈ Finset.Ico (0 : ℤ) k,
      (symmA 0 k i).card = 3 ∧ (symmA 0 k i).sum id = 0 := by
    intro i hi
    obtain ⟨hi0, hik⟩ := Finset.mem_Ico.mp hi
    simp only [symmA]
    exact card_sum_triple (by omega) (by omega) (by omega) (by ring)
  have hB : ∀ i ∈ Finset.Ico (0 : ℤ) k,
      (symmB 0 k i).card = 3 ∧ (symmB 0 k i).sum id = 0 := by
    intro i hi
    obtain ⟨hi0, hik⟩ := Finset.mem_Ico.mp hi
    simp only [symmB]
    exact card_sum_triple (by omega) (by omega) (by omega) (by ring)
  have hAz := zeroPartition_image (Finset.Ico (0 : ℤ) k) (symmA 0 k) hA
    (fun i hi j hj hij => symmA_disjoint (Finset.mem_Ico.mp hi) (Finset.mem_Ico.mp hj) hij)
  have hBz := zeroPartition_image (Finset.Ico (0 : ℤ) k) (symmB 0 k) hB
    (fun i hi j hj hij => symmB_disjoint (Finset.mem_Ico.mp hi) (Finset.mem_Ico.mp hj) hij)
  have hd : Disjoint ((Finset.Ico (0 : ℤ) k).biUnion (symmA 0 k))
      ((Finset.Ico (0 : ℤ) k).biUnion (symmB 0 k)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx'
    exact Finset.disjoint_left.mp
      (symmAB_disjoint (Finset.mem_Ico.mp hi) (Finset.mem_Ico.mp hj)) hxi hxj
  have hu := hAz.union hBz hd
  rw [symmetric_core_coverage 0 k hk] at hu
  have hset : (Finset.Icc (0 - 3 * k) (0 + 3 * k)).erase 0 = symInterval k := by
    ext x
    simp only [symInterval, Finset.mem_erase, Finset.mem_Icc]
    omega
  rw [hset] at hu
  exact hu

/-- The blockwise negation of a family of blocks. -/
def negBlocks (zs : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  zs.image (fun b => b.image (fun x => -x))

/-- Negating every entry of every block of a partition into zero-sum triples gives a partition of
the negated set into zero-sum triples. -/
theorem ZeroPartition.negBlocks {s : Finset ℤ} {zs : Finset (Finset ℤ)} (h : ZeroPartition s zs) :
    ZeroPartition (s.image (fun x => -x)) (negBlocks zs) := by
  have hneg : Function.Injective (fun x : ℤ => -x) := fun a b hab => by
    simp only at hab
    omega
  have hz : ∀ b ∈ zs, (b.image (fun x : ℤ => -x)).card = 3 ∧
      (b.image (fun x : ℤ => -x)).sum id = 0 := by
    intro b hb
    obtain ⟨hcard, hsum⟩ := h.2.2 b hb
    refine ⟨by rw [Finset.card_image_of_injective _ hneg]; exact hcard, ?_⟩
    rw [Finset.sum_image (fun x _ y _ hxy => hneg hxy)]
    have hsum' : ∑ x ∈ b, (x : ℤ) = 0 := hsum
    simp only [id_eq]
    rw [Finset.sum_neg_distrib (fun x : ℤ => x), hsum', neg_zero]
  have hd : ∀ b ∈ zs, ∀ c ∈ zs, b ≠ c →
      Disjoint (b.image (fun x : ℤ => -x)) (c.image (fun x : ℤ => -x)) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact Finset.disjoint_left.mp (h.2.1 b hb c hc hbc) (mem_neg_image.mp hx)
      (mem_neg_image.mp hx')
  have himg := zeroPartition_image zs (fun b => b.image (fun x : ℤ => -x)) hz hd
  have hset : zs.biUnion (fun b => b.image (fun x : ℤ => -x)) = s.image (fun x => -x) := by
    ext x
    simp only [Finset.mem_biUnion, mem_neg_image]
    rw [← h.1]
    simp only [Finset.mem_biUnion, id_eq]
  rw [hset] at himg
  exact himg

/-- The centered interval with its centre removed is symmetric. -/
theorem symInterval_neg (k : ℤ) : (symInterval k).image (fun x => -x) = symInterval k := by
  ext x
  simp only [symInterval, Finset.mem_image, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨u, ⟨hu0, hu1, hu2⟩, rfl⟩
    omega
  · intro hx
    exact ⟨-x, by omega, by omega⟩

/-- The symmetric family differs from its own negation: the block of the smallest entry is not the
negation of any block of the family. -/
theorem symFamily_ne_neg (k : ℤ) (hk : 2 ≤ k) : symFamily k ≠ negBlocks (symFamily k) := by
  sorry

/-- The first trade, at `k = 3h`: the three blocks of the second family with indices `0`, `h` and
`2h` are replaced by three other zero-sum triples on the same nine entries. -/
def tradeI (h : ℤ) : Finset (Finset ℤ) :=
  (symFamily (3 * h) \ {symmB 0 (3 * h) 0, symmB 0 (3 * h) h, symmB 0 (3 * h) (2 * h)}) ∪
    {{-(6 * h), -h, 7 * h}, {-(5 * h), -(4 * h), 9 * h}, {-(3 * h), -(2 * h), 5 * h}}

/-- The second trade, at `k = 3h + 1`: the blocks `A 0`, `A (2h + 1)` and `B (h + 1)` are replaced
by three other zero-sum triples on the same nine entries. -/
def tradeII (h : ℤ) : Finset (Finset ℤ) :=
  (symFamily (3 * h + 1) \
      {symmA 0 (3 * h + 1) 0, symmA 0 (3 * h + 1) (2 * h + 1), symmB 0 (3 * h + 1) (h + 1)}) ∪
    {{-(9 * h + 3), 2 * h + 2, 7 * h + 1}, {-(7 * h + 2), -(2 * h), 9 * h + 2},
      {-(5 * h + 1), 1, 5 * h}}

/-- The third trade, at `k = 3h + 2` with `h ≥ 2`: the blocks `A h`, `B (2h + 2)` and `B (3h + 1)`
are replaced by three other zero-sum triples on the same nine entries. -/
def tradeIII (h : ℤ) : Finset (Finset ℤ) :=
  (symFamily (3 * h + 2) \
      {symmA 0 (3 * h + 2) h, symmB 0 (3 * h + 2) (2 * h + 2), symmB 0 (3 * h + 2) (3 * h + 1)}) ∪
    {{-(8 * h + 6), 5 * h + 2, 3 * h + 4}, {-(4 * h + 2), -(3 * h + 3), 7 * h + 5},
      {-h, -1, h + 1}}

/-- The first trade is a partition into zero-sum triples of the same centered interval. -/
theorem tradeI_zeroPartition (h : ℤ) (hh : 1 ≤ h) :
    ZeroPartition (symInterval (3 * h)) (tradeI h) := by
  sorry

/-- The first trade differs from the symmetric family. -/
theorem tradeI_ne_family (h : ℤ) (hh : 1 ≤ h) : tradeI h ≠ symFamily (3 * h) := by
  sorry

/-- The first trade differs from the negation of the symmetric family. -/
theorem tradeI_ne_neg (h : ℤ) (hh : 1 ≤ h) : tradeI h ≠ negBlocks (symFamily (3 * h)) := by
  sorry

/-- The second trade is a partition into zero-sum triples of the same centered interval. -/
theorem tradeII_zeroPartition (h : ℤ) (hh : 1 ≤ h) :
    ZeroPartition (symInterval (3 * h + 1)) (tradeII h) := by
  sorry

/-- The second trade differs from the symmetric family. -/
theorem tradeII_ne_family (h : ℤ) (hh : 1 ≤ h) : tradeII h ≠ symFamily (3 * h + 1) := by
  sorry

/-- The second trade differs from the negation of the symmetric family. -/
theorem tradeII_ne_neg (h : ℤ) (hh : 1 ≤ h) : tradeII h ≠ negBlocks (symFamily (3 * h + 1)) := by
  sorry

/-- The third trade is a partition into zero-sum triples of the same centered interval. -/
theorem tradeIII_zeroPartition (h : ℤ) (hh : 2 ≤ h) :
    ZeroPartition (symInterval (3 * h + 2)) (tradeIII h) := by
  sorry

/-- The third trade differs from the symmetric family. -/
theorem tradeIII_ne_family (h : ℤ) (hh : 2 ≤ h) : tradeIII h ≠ symFamily (3 * h + 2) := by
  sorry

/-- The third trade differs from the negation of the symmetric family. -/
theorem tradeIII_ne_neg (h : ℤ) (hh : 2 ≤ h) : tradeIII h ≠ negBlocks (symFamily (3 * h + 2)) := by
  sorry

/-- Three pairwise distinct partitions of the centered interval with its centre removed, for every
`k ≥ 3`. -/
theorem threeZero_sym (k : ℤ) (hk : 3 ≤ k) : ThreeZero (symInterval k) := by
  sorry

/-- Three symmetric frames at the two offsets built from a symmetric interval: the offset `3k`, and
the offset `3k + 1` after appending the triple through the centre. -/
theorem threeFrameA_of_threeZero_sym {k : ℤ} (hk : 0 ≤ k) (h : ThreeZero (symInterval k)) :
    ThreeFrameA (3 * k) ∧ ThreeFrameA (3 * k + 1) := by
  sorry

/-- Three symmetric frames at offset seven. -/
theorem threeFrameA_seven : ThreeFrameA 7 := by
  sorry

/-- Three symmetric frames at every offset from seven on that is congruent to zero or one modulo
three. -/
theorem threeFrameA_of_mod (r : ℤ) (hr : 7 ≤ r) (hmod : r % 3 = 0 ∨ r % 3 = 1) :
    ThreeFrameA r := by
  sorry

end

end GNM

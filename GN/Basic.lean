import Mathlib

namespace GN

noncomputable section

/-- A partition of an integer set into nonempty blocks of size at most three,
with every block sum a nonnegative integral power of three. -/
def GoodOn (s : Finset ℤ) (blocks : Finset (Finset ℤ)) : Prop :=
  blocks.biUnion id = s ∧
  (∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c) ∧
  ∀ b ∈ blocks, b.Nonempty ∧ b.card ≤ 3 ∧ ∃ k : ℕ, b.sum id = (3 : ℤ)^k

/-- Existence of a good partition of a specified finite integer set. -/
def HasGood (s : Finset ℤ) : Prop := ∃ blocks, GoodOn s blocks

/-- The positive integer interval {1,...,n}; n=0 gives the empty set. -/
def interval (n : ℕ) : Finset ℤ := Finset.Icc 1 (n : ℤ)

/-- The three conditions on a single good block. -/
def GoodBlock (b : Finset ℤ) : Prop :=
  b.Nonempty ∧ b.card ≤ 3 ∧ ∃ k : ℕ, b.sum id = (3 : ℤ)^k

@[simp] theorem interval_zero : interval 0 = ∅ := by simp [interval]

 theorem GoodOn.block {s : Finset ℤ} {blocks : Finset (Finset ℤ)}
    (h : GoodOn s blocks) {b : Finset ℤ} (hb : b ∈ blocks) : GoodBlock b := h.2.2 b hb

 theorem GoodOn.subset {s : Finset ℤ} {blocks : Finset (Finset ℤ)}
    (h : GoodOn s blocks) {b : Finset ℤ} (hb : b ∈ blocks) : b ⊆ s := by
  intro x hx
  rw [← h.1]
  exact Finset.mem_biUnion.mpr ⟨b, hb, hx⟩

 theorem goodOn_empty : GoodOn ∅ ∅ := by simp [GoodOn]

 theorem hasGood_empty : HasGood ∅ := ⟨∅, goodOn_empty⟩

 theorem GoodOn.union {s t : Finset ℤ} {bs cs : Finset (Finset ℤ)}
    (hs : GoodOn s bs) (ht : GoodOn t cs) (hst : Disjoint s t) :
    GoodOn (s ∪ t) (bs ∪ cs) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.union_biUnion, hs.1, ht.1]
  · intro b hb c hc hbc
    rcases Finset.mem_union.mp hb with hb | hb <;>
      rcases Finset.mem_union.mp hc with hc | hc
    · exact hs.2.1 b hb c hc hbc
    · exact hst.mono (hs.subset hb) (ht.subset hc)
    · exact hst.symm.mono (ht.subset hb) (hs.subset hc)
    · exact ht.2.1 b hb c hc hbc
  · intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hs.2.2 b hb
    · exact ht.2.2 b hb

 theorem HasGood.union {s t : Finset ℤ} (hs : HasGood s) (ht : HasGood t)
    (hst : Disjoint s t) : HasGood (s ∪ t) := by
  obtain ⟨bs, hbs⟩ := hs
  obtain ⟨cs, hcs⟩ := ht
  exact ⟨bs ∪ cs, hbs.union hcs hst⟩

 theorem GoodBlock.goodOn {b : Finset ℤ} (hb : GoodBlock b) : GoodOn b {b} := by
  simpa [GoodOn, GoodBlock] using hb

 theorem GoodBlock.hasGood {b : Finset ℤ} (hb : GoodBlock b) : HasGood b :=
  ⟨{b}, hb.goodOn⟩

 theorem goodBlock_singleton (k : ℕ) : GoodBlock {(3 : ℤ)^k} := by
  refine ⟨by simp, by simp, k, ?_⟩
  simp

 theorem goodBlock_pair {x y : ℤ} (hxy : x ≠ y) {k : ℕ}
    (hs : x + y = (3 : ℤ)^k) : GoodBlock {x, y} := by
  refine ⟨by simp, ?_, k, ?_⟩
  · simp [Finset.card_insert_of_notMem, hxy]
  · simpa [Finset.sum_insert, hxy] using hs

 theorem goodBlock_triple {x y z : ℤ} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) {k : ℕ} (hs : x + y + z = (3 : ℤ)^k) :
    GoodBlock {x, y, z} := by
  refine ⟨by simp, ?_, k, ?_⟩
  · simp [Finset.card_insert_of_notMem, hxy, hxz, hyz]
  · simpa [Finset.sum_insert, hxy, hxz, hyz, add_assoc] using hs

/-- Assemble an indexed family of disjoint good blocks. -/
 theorem goodOn_image {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → Finset ℤ) (hgood : ∀ i ∈ u, GoodBlock (f i))
    (hdisj : ∀ i ∈ u, ∀ j ∈ u, i ≠ j → Disjoint (f i) (f j)) :
    GoodOn (u.biUnion f) (u.image f) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp
  · intro b hb c hc hbc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact hdisj i hi j hj (fun hij => hbc (congrArg f hij))
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact hgood i hi

 theorem hasGood_biUnion {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → Finset ℤ) (hgood : ∀ i ∈ u, GoodBlock (f i))
    (hdisj : ∀ i ∈ u, ∀ j ∈ u, i ≠ j → Disjoint (f i) (f j)) :
    HasGood (u.biUnion f) := ⟨u.image f, goodOn_image u f hgood hdisj⟩

end

end GN

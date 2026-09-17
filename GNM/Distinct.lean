import GNM.Basic

/-!
# Three-fold distinctness

The lower bounds of the classification all come from three constructions that differ in a component
that can be read back off the result. At the level of permutations that component is the permutation
itself, so the useful predicate is "three pairwise distinct permutations of a prescribed support
with a prescribed set of displacements"; at the level of frames it is "three pairwise distinct
partitions of a prescribed set into zero-sum triples". This module fixes those predicates and the
dictionary between the three coordinate systems in use: the centered interval with a hole, the
positional interval `[1, 2k + 1]` with a hole, and the interval `[1, 2q]` with no hole.
-/

namespace GNM

open GN

noncomputable section

/-- Three pairwise distinct permutations of `S` whose displacements are exactly `D`. -/
def ThreePWD (S D : Finset ℤ) : Prop :=
  ∃ σ₁ σ₂ σ₃ : ℤ → ℤ, PermutationWithDifferences S D σ₁ ∧ PermutationWithDifferences S D σ₂ ∧
    PermutationWithDifferences S D σ₃ ∧ (∃ x ∈ S, σ₁ x ≠ σ₂ x) ∧ (∃ x ∈ S, σ₁ x ≠ σ₃ x) ∧
    (∃ x ∈ S, σ₂ x ≠ σ₃ x)

/-- Three pairwise distinct displacement permutations of the centered interval `[-k, k]` with the
hole `j`. -/
def ThreeDisp (k j : ℤ) : Prop :=
  ThreePWD (displacementDomain k j) ((Finset.Icc (-k) k).erase 0)

/-- A displacement permutation is exactly a permutation with differences on the centered domain. -/
theorem displacementPermutation_iff (k j : ℤ) (σ : ℤ → ℤ) :
    DisplacementPermutation k j σ ↔
      PermutationWithDifferences (displacementDomain k j) ((Finset.Icc (-k) k).erase 0) σ :=
  Iff.rfl

/-- Three pairwise distinct permutations of `[1, 2q]` with displacements `±1, …, ±q`. -/
def ThreeM (q : ℤ) : Prop := ThreePWD (Finset.Icc 1 (2 * q)) ((Finset.Icc (-q) q).erase 0)

/-- Three pairwise distinct permutations of `[1, 2k + 1]` with the position `H` removed, with
displacements `±1, …, ±k`. -/
def ThreeA (k H : ℤ) : Prop :=
  ThreePWD ((Finset.Icc 1 (2 * k + 1)).erase H) ((Finset.Icc (-k) k).erase 0)

/-- Translating every position preserves three-fold distinctness. -/
theorem ThreePWD.translate {S D : Finset ℤ} (c : ℤ) (h : ThreePWD S D) :
    ThreePWD (S.image (fun x => c + x)) D := by
  obtain ⟨σ₁, σ₂, σ₃, h₁, h₂, h₃, ⟨x₁₂, hx₁₂, hne₁₂⟩, ⟨x₁₃, hx₁₃, hne₁₃⟩, ⟨x₂₃, hx₂₃, hne₂₃⟩⟩ := h
  refine ⟨fun x => c + σ₁ (x - c), fun x => c + σ₂ (x - c), fun x => c + σ₃ (x - c),
    h₁.translate c, h₂.translate c, h₃.translate c, ?_, ?_, ?_⟩
  · refine ⟨c + x₁₂, Finset.mem_image.mpr ⟨x₁₂, hx₁₂, rfl⟩, ?_⟩
    simp only [add_sub_cancel_left]
    omega
  · refine ⟨c + x₁₃, Finset.mem_image.mpr ⟨x₁₃, hx₁₃, rfl⟩, ?_⟩
    simp only [add_sub_cancel_left]
    omega
  · refine ⟨c + x₂₃, Finset.mem_image.mpr ⟨x₂₃, hx₂₃, rfl⟩, ?_⟩
    simp only [add_sub_cancel_left]
    omega

/-- Negating every position preserves three-fold distinctness, with the displacements negated. -/
theorem ThreePWD.negate {S D : Finset ℤ} (h : ThreePWD S D) :
    ThreePWD (S.image (fun x => -x)) (D.image (fun x => -x)) := by
  obtain ⟨σ₁, σ₂, σ₃, h₁, h₂, h₃, ⟨x₁₂, hx₁₂, hne₁₂⟩, ⟨x₁₃, hx₁₃, hne₁₃⟩, ⟨x₂₃, hx₂₃, hne₂₃⟩⟩ := h
  refine ⟨fun x => -σ₁ (-x), fun x => -σ₂ (-x), fun x => -σ₃ (-x),
    h₁.negate, h₂.negate, h₃.negate, ?_, ?_, ?_⟩
  · refine ⟨-x₁₂, Finset.mem_image.mpr ⟨x₁₂, hx₁₂, rfl⟩, ?_⟩
    simp only [neg_neg]
    omega
  · refine ⟨-x₁₃, Finset.mem_image.mpr ⟨x₁₃, hx₁₃, rfl⟩, ?_⟩
    simp only [neg_neg]
    omega
  · refine ⟨-x₂₃, Finset.mem_image.mpr ⟨x₂₃, hx₂₃, rfl⟩, ?_⟩
    simp only [neg_neg]
    omega

/-- Reflecting the positions about `c / 2` preserves three-fold distinctness, with the displacements
negated. -/
theorem ThreePWD.reflect {S D : Finset ℤ} (c : ℤ) (h : ThreePWD S D) :
    ThreePWD (S.image (fun x => c - x)) (D.image (fun x => -x)) := by
  have ht := (h.negate).translate c
  rw [Finset.image_image] at ht
  have hfun : ((fun y : ℤ => c + y) ∘ (fun x : ℤ => -x)) = (fun x : ℤ => c - x) := by
    funext x
    simp only [Function.comp_apply]
    omega
  rwa [hfun] at ht

/-- The interval `[1, 2q]` is the positional interval `[1, 2q + 1]` with its last position as the
hole. -/
theorem threeM_iff_threeA (q : ℤ) (hq : 0 ≤ q) : ThreeM q ↔ ThreeA q (2 * q + 1) := by
  have he : (Finset.Icc 1 (2 * q + 1)).erase (2 * q + 1) = Finset.Icc 1 (2 * q) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  unfold ThreeM ThreeA
  rw [he]

/-- The centered hole `j` is the position `j + k + 1`. -/
theorem threeA_of_threeDisp {k j : ℤ} (h : ThreeDisp k j) : ThreeA k (j + k + 1) := by
  have ht := ThreePWD.translate (k + 1) h
  have he : (displacementDomain k j).image (fun x => k + 1 + x)
      = (Finset.Icc 1 (2 * k + 1)).erase (j + k + 1) := by
    ext x
    simp only [Finset.mem_image, mem_displacementDomain, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · rintro ⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩
      omega
    · intro hx
      exact ⟨x - (k + 1), by omega, by omega⟩
  unfold ThreeA
  rw [← he]
  exact ht

/-- The position `H` is the centered hole `H − k − 1`. -/
theorem threeDisp_of_threeA {k H : ℤ} (h : ThreeA k H) : ThreeDisp k (H - k - 1) := by
  have ht := ThreePWD.translate (-(k + 1)) h
  have he : ((Finset.Icc 1 (2 * k + 1)).erase H).image (fun x => -(k + 1) + x)
      = displacementDomain k (H - k - 1) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_Icc, mem_displacementDomain]
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      omega
    · intro hx
      exact ⟨x + (k + 1), by omega, by omega⟩
  unfold ThreeDisp
  rw [← he]
  exact ht

/-- The centered picture is symmetric under negating the hole. -/
theorem ThreeDisp.neg {k j : ℤ} (h : ThreeDisp k j) : ThreeDisp k (-j) := by
  have hn := ThreePWD.negate h
  have hS : (displacementDomain k j).image (fun x => -x) = displacementDomain k (-j) := by
    ext x
    simp only [Finset.mem_image, mem_displacementDomain]
    constructor
    · rintro ⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩
      omega
    · intro hx
      exact ⟨-x, by omega, by omega⟩
  have hD : ((Finset.Icc (-k) k).erase 0).image (fun x => -x) = (Finset.Icc (-k) k).erase 0 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      omega
    · intro hx
      exact ⟨-x, by omega, by omega⟩
  unfold ThreeDisp
  rw [← hS, ← hD]
  exact hn

/-- Three pairwise distinct partitions of a set into zero-sum triples. -/
def ThreeZero (s : Finset ℤ) : Prop :=
  ∃ z₁ z₂ z₃ : Finset (Finset ℤ), ZeroPartition s z₁ ∧ ZeroPartition s z₂ ∧ ZeroPartition s z₃ ∧
    z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃

/-- Three pairwise distinct signed frames on the vertex set of the offset `r` with partner `a`. -/
def ThreeFrames (r a : ℤ) : Prop := ThreeZero (signedVertices r a)

/-- The vertex set of a symmetric frame at offset `r`: the centered interval `[-r, r]`, with zero
removed exactly when three divides `r`. -/
def frameSet (r : ℤ) : Finset ℤ :=
  if r % 3 = 0 then (Finset.Icc (-r) r).erase 0 else Finset.Icc (-r) r

/-- Three pairwise distinct symmetric frames at offset `r`. -/
def ThreeFrameA (r : ℤ) : Prop := ThreeZero (frameSet r)

end

end GNM

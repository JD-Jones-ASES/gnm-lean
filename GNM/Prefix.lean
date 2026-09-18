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
  obtain ⟨π, hπ⟩ := hl.exists_permutation
  have hd := hl.defect_pos
  have hk := hl.order_nonempty
  have hh := hl.hole_mem
  have ht := hπ.translate (2 * (d - 1))
  have hST : Disjoint (Finset.Icc 1 (2 * (d - 1)))
      (((Finset.Icc 1 (2 * (k - d + 1) + 1)).erase h).image (fun x => 2 * (d - 1) + x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx
    simp only [mem_add_image, Finset.mem_erase, Finset.mem_Icc] at hx'
    omega
  have hDE : Disjoint ((Finset.Icc (-(d - 1)) (d - 1)).erase 0) (signedDifferences d k) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_erase, Finset.mem_Icc] at hx
    simp only [signedDifferences, Finset.mem_union, Finset.mem_Icc] at hx'
    omega
  have hglue := hτ.glue ht hST hDE
  have hS : Finset.Icc 1 (2 * (d - 1)) ∪
      (((Finset.Icc 1 (2 * (k - d + 1) + 1)).erase h).image (fun x => 2 * (d - 1) + x)) =
      (Finset.Icc 1 (2 * k + 1)).erase (h + 2 * (d - 1)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, mem_add_image, Finset.mem_erase]
    omega
  have hD : ((Finset.Icc (-(d - 1)) (d - 1)).erase 0) ∪ signedDifferences d k =
      (Finset.Icc (-k) k).erase 0 := by
    ext x
    simp only [signedDifferences, Finset.mem_union, Finset.mem_Icc, Finset.mem_erase]
    omega
  rw [hS, hD] at hglue
  refine ⟨_, hglue, ?_⟩
  intro x hx
  simp only [if_pos hx]

/-- Three distinct prefixes glued to one pairing give three distinct permutations. -/
theorem threeA_of_pairing {d k h : ℤ} {ps : Finset (ℤ × ℤ)} (hl : LangfordPairing d k h ps)
    (hM : ThreeM (d - 1)) : ThreeA k (h + 2 * (d - 1)) := by
  obtain ⟨τ₁, τ₂, τ₃, h₁, h₂, h₃, ⟨x₁₂, hx₁₂, hne₁₂⟩, ⟨x₁₃, hx₁₃, hne₁₃⟩,
    ⟨x₂₃, hx₂₃, hne₂₃⟩⟩ := hM
  have hd := hl.defect_pos
  have hk := hl.order_nonempty
  have hh := hl.hole_mem
  have hsub : ∀ x ∈ Finset.Icc (1 : ℤ) (2 * (d - 1)),
      x ∈ (Finset.Icc 1 (2 * k + 1)).erase (h + 2 * (d - 1)) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  obtain ⟨σ₁, hσ₁, ha₁⟩ := with_prefix hl h₁
  obtain ⟨σ₂, hσ₂, ha₂⟩ := with_prefix hl h₂
  obtain ⟨σ₃, hσ₃, ha₃⟩ := with_prefix hl h₃
  refine ⟨σ₁, σ₂, σ₃, hσ₁, hσ₂, hσ₃, ⟨x₁₂, hsub x₁₂ hx₁₂, ?_⟩, ⟨x₁₃, hsub x₁₃ hx₁₃, ?_⟩,
    ⟨x₂₃, hsub x₂₃ hx₂₃, ?_⟩⟩
  · rw [ha₁ x₁₂ hx₁₂, ha₂ x₁₂ hx₁₂]
    exact hne₁₂
  · rw [ha₁ x₁₃ hx₁₃, ha₃ x₁₃ hx₁₃]
    exact hne₁₃
  · rw [ha₂ x₂₃ hx₂₃, ha₃ x₂₃ hx₂₃]
    exact hne₂₃

/-- Two pairing families of opposite hole parity, whose defects differ by two, give three distinct
permutations at every suffix position: the hole parity selects the family, and the prefix supplies
the three permutations. -/
private theorem threeA_of_opposite_pairings {d k H p : ℤ}
    (_hd : 3 ≤ d) (hH : 2 * d - 1 ≤ H ∧ H ≤ 2 * k + 1)
    (hM1 : ThreeM (d - 1)) (hM3 : ThreeM (d - 3))
    (hlow : ∀ h : ℤ, (1 ≤ h ∧ h ≤ 2 * (k - d + 1) + 1) → h % 2 = p % 2 →
      ∃ ps, LangfordPairing d k h ps)
    (hhigh : ∀ h : ℤ, (1 ≤ h ∧ h ≤ 2 * (k - (d - 2) + 1) + 1) → h % 2 = (p + 1) % 2 →
      ∃ ps, LangfordPairing (d - 2) k h ps) :
    ThreeA k H := by
  let h := H - 2 * (d - 1)
  by_cases hp : h % 2 = p % 2
  · obtain ⟨ps, hps⟩ := hlow h (by dsimp [h]; omega) hp
    have ha := threeA_of_pairing hps hM1
    have he : h + 2 * (d - 1) = H := by dsimp [h]; ring
    rw [he] at ha
    exact ha
  · obtain ⟨ps, hps⟩ := hhigh (h + 4) (by dsimp [h]; omega) (by omega)
    have hM3' : ThreeM (d - 2 - 1) := by
      have he : d - 2 - 1 = d - 3 := by ring
      rw [he]
      exact hM3
    have ha := threeA_of_pairing hps hM3'
    have he : h + 4 + 2 * (d - 2 - 1) = H := by dsimp [h]; ring
    rw [he] at ha
    exact ha

/-- The upper-half holes with a variable prefix: the six explicit pairing families of the underlying
development, with the prefix half-length `d − 1` or `d − 3` for `d = (k + 2) / 3 ≥ 8`. -/
theorem threeA_high {k H : ℤ} (hk : 22 ≤ k) (hH : k + 1 ≤ H ∧ H ≤ 2 * k + 1)
    (hM : ∀ q : ℤ, 5 ≤ q → q < k → ThreeM q) : ThreeA k H := by
  let d := (k + 2) / 3
  have hd : 8 ≤ d := by dsimp [d]; omega
  have hi : k = 3 * d - 2 ∨ k = 3 * d - 1 ∨ k = 3 * d := by dsimp [d]; omega
  have hbound : 2 * d - 1 ≤ H ∧ H ≤ 2 * k + 1 := by omega
  have hM1 : ThreeM (d - 1) := hM (d - 1) (by omega) (by omega)
  have hM3 : ThreeM (d - 3) := hM (d - 3) (by omega) (by omega)
  rcases hi with hi | hi | hi
  · apply threeA_of_opposite_pairings (d := d) (p := 1) (by omega) hbound hM1 hM3
    · intro h hh hp
      obtain ⟨ps, hps⟩ := minimal_langford_family.mono (show (1 : ℤ) ≤ 8 by omega) d hd h
        (by omega) (by omega)
      have he : 3 * d - 2 + 0 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
    · intro h hh hp
      obtain ⟨ps, hps⟩ := excess6_langford_family (d - 2) (by omega) h (by omega)
        (by dsimp only; omega)
      have he : 3 * (d - 2) - 2 + 6 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
  · apply threeA_of_opposite_pairings (d := d) (p := d + 1) (by omega) hbound hM1 hM3
    · intro h hh hp
      obtain ⟨ps, hps⟩ := near1_langford_family d hd h (by omega) hp
      have he : 3 * d - 2 + 1 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
    · intro h hh hp
      obtain ⟨ps, hps⟩ := excess7_langford_family (d - 2) (by omega) h (by omega)
        (by dsimp only; omega)
      have he : 3 * (d - 2) - 2 + 7 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
  · apply threeA_of_opposite_pairings (d := d) (p := 0) (by omega) hbound hM1 hM3
    · intro h hh hp
      obtain ⟨ps, hps⟩ := near2_langford_family d hd h (by omega) hp
      have he : 3 * d - 2 + 2 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
    · intro h hh hp
      obtain ⟨ps, hps⟩ := excess8_langford_family (d - 2) (by omega) h (by omega)
        (by dsimp only; omega)
      have he : 3 * (d - 2) - 2 + 8 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩

set_option linter.unusedVariables false in
/-- Reflecting the positions moves the hole `H` to `2k + 2 − H`. -/
theorem threeA_reflect {k H : ℤ} (hk : 0 ≤ k) (h : ThreeA k H) : ThreeA k (2 * k + 2 - H) := by
  have hr := ThreePWD.reflect (2 * k + 2) h
  have hS : (((Finset.Icc 1 (2 * k + 1)).erase H).image (fun x => 2 * k + 2 - x)) =
      (Finset.Icc 1 (2 * k + 1)).erase (2 * k + 2 - H) := by
    ext x
    simp only [mem_sub_image, Finset.mem_erase, Finset.mem_Icc]
    omega
  have hD : (((Finset.Icc (-k) k).erase 0).image (fun x => -x)) = (Finset.Icc (-k) k).erase 0 := by
    ext x
    simp only [mem_neg_image, Finset.mem_erase, Finset.mem_Icc]
    omega
  rw [hS, hD] at hr
  exact hr

/-- Three permutations of `[1, 2q]` with displacements `±1, …, ±q`, for every `q ≥ 5`. -/
theorem threeM_all (q : ℤ) (hq : 5 ≤ q) : ThreeM q := by
  have main : ∀ n : ℕ, ∀ p : ℤ, p.toNat ≤ n → 5 ≤ p → ThreeM p := by
    intro n
    induction n with
    | zero =>
      intro p hpn hp
      exfalso
      omega
    | succ n ih =>
      intro p hpn hp
      by_cases h21 : p ≤ 21
      · have hdisp := threeDisp_of_le_21 (k := p) (j := p) (by omega) h21 ⟨by omega, le_refl p⟩
        have ha := threeA_of_threeDisp hdisp
        have he : p + p + 1 = 2 * p + 1 := by ring
        rw [he] at ha
        exact (threeM_iff_threeA p (by omega)).mpr ha
      · have hM : ∀ r : ℤ, 5 ≤ r → r < p → ThreeM r := fun r hr hrp => ih r (by omega) hr
        have ha := threeA_high (k := p) (H := 2 * p + 1) (by omega) ⟨by omega, by omega⟩ hM
        exact (threeM_iff_threeA p (by omega)).mpr ha
  exact main q.toNat q le_rfl hq

/-- Three permutations of `[1, 2k + 1]` with any one position removed, for every `k ≥ 4`. -/
theorem threeA_all {k H : ℤ} (hk : 4 ≤ k) (hH : 1 ≤ H ∧ H ≤ 2 * k + 1) : ThreeA k H := by
  by_cases h21 : k ≤ 21
  · have hdisp := threeDisp_of_le_21 (k := k) (j := H - k - 1) hk h21 ⟨by omega, by omega⟩
    have ha := threeA_of_threeDisp hdisp
    have he : H - k - 1 + k + 1 = H := by ring
    rw [he] at ha
    exact ha
  · by_cases hup : k + 1 ≤ H
    · exact threeA_high (by omega) ⟨hup, hH.2⟩ (fun q hq5 _ => threeM_all q hq5)
    · have hb := threeA_high (k := k) (H := 2 * k + 2 - H) (by omega) ⟨by omega, by omega⟩
        (fun q hq5 _ => threeM_all q hq5)
      have hr := threeA_reflect (show (0 : ℤ) ≤ k by omega) hb
      have he : 2 * k + 2 - (2 * k + 2 - H) = H := by ring
      rw [he] at hr
      exact hr

/-- Three displacement permutations at every hole of the centered interval, for every `k ≥ 4`. -/
theorem threeDisp_all {k j : ℤ} (hk : 4 ≤ k) (hj : -k ≤ j ∧ j ≤ k) : ThreeDisp k j := by
  have ha := threeA_all (k := k) (H := j + k + 1) hk ⟨by omega, by omega⟩
  have hd := threeDisp_of_threeA ha
  have he : j + k + 1 - k - 1 = j := by ring
  rw [he] at hd
  exact hd

end

end GNM

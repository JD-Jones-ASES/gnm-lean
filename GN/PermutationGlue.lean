import GN.Doubling
import GN.Langford

namespace GN
noncomputable section

/-- A permutation of a finite support with a prescribed set of distinct displacements. -/
def PermutationWithDifferences (S D : Finset ℤ) (σ : ℤ → ℤ) : Prop :=
  Set.BijOn σ S S ∧ Set.BijOn (fun x => σ x-x) S D

@[simp] theorem mem_add_image {S : Finset ℤ} {c x : ℤ} :
    x ∈ S.image (fun y => c+y) ↔ x-c ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
    have he : y = x-c := by omega
    simpa only [he] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x-c, hx, by omega⟩

/-- Translating all positions preserves the signed displacements. -/
theorem PermutationWithDifferences.translate {S D : Finset ℤ} {σ : ℤ → ℤ}
    (h : PermutationWithDifferences S D σ) (c : ℤ) :
    PermutationWithDifferences (S.image (fun x => c+x)) D
      (fun x => c+σ (x-c)) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hxS := mem_add_image.mp hx
      apply mem_add_image.mpr
      simpa only [add_sub_cancel_left, Finset.mem_coe] using h.1.mapsTo hxS
    · intro x hx y hy hxy
      have heq : σ (x-c) = σ (y-c) := by dsimp only at hxy; omega
      have he := h.1.injOn (mem_add_image.mp hx) (mem_add_image.mp hy) heq
      omega
    · intro y hy
      obtain ⟨x, hx, heq⟩ := h.1.surjOn (mem_add_image.mp hy)
      refine ⟨c+x, mem_add_image.mpr ?_, ?_⟩
      · simpa only [add_sub_cancel_left, Finset.mem_coe] using hx
      · dsimp only
        have he : c+x-c = x := by omega
        rw [he]
        omega
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have heq : c+σ (x-c)-x = σ (x-c)-(x-c) := by ring
      dsimp only
      rw [heq]
      exact h.2.mapsTo (mem_add_image.mp hx)
    · intro x hx y hy hxy
      have heq : σ (x-c)-(x-c) = σ (y-c)-(y-c) := by dsimp only at hxy; omega
      have he := h.2.injOn (mem_add_image.mp hx) (mem_add_image.mp hy) heq
      omega
    · intro y hy
      obtain ⟨x, hx, heq⟩ := h.2.surjOn hy
      refine ⟨c+x, mem_add_image.mpr ?_, ?_⟩
      · simpa only [add_sub_cancel_left, Finset.mem_coe] using hx
      · dsimp only at heq ⊢
        have he : c+x-c = x := by omega
        rw [he]
        omega

/-- Glue two bijections on disjoint finite source and target sets. -/
theorem bijOn_piecewise_union {S T U V : Finset ℤ} {f g : ℤ → ℤ}
    (hST : Disjoint S T) (hUV : Disjoint U V)
    (hf : Set.BijOn f S U) (hg : Set.BijOn g T V) :
    Set.BijOn (fun x => if x ∈ S then f x else g x)
      (↑(S ∪ T : Finset ℤ)) (↑(U ∪ V : Finset ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ S ∨ x ∈ T := by simpa only [Finset.mem_coe, Finset.mem_union] using hx
    by_cases hxS : x ∈ S
    · simp only [if_pos hxS, Finset.mem_coe, Finset.mem_union]
      exact Or.inl (hf.mapsTo hxS)
    · have hxT : x ∈ T := hx'.resolve_left hxS
      simp only [if_neg hxS, Finset.mem_coe, Finset.mem_union]
      exact Or.inr (hg.mapsTo hxT)
  · intro x hx y hy hxy
    have hx' : x ∈ S ∨ x ∈ T := by simpa only [Finset.mem_coe, Finset.mem_union] using hx
    have hy' : y ∈ S ∨ y ∈ T := by simpa only [Finset.mem_coe, Finset.mem_union] using hy
    by_cases hxS : x ∈ S <;> by_cases hyS : y ∈ S
    · simp only [if_pos hxS, if_pos hyS] at hxy
      exact hf.injOn hxS hyS hxy
    · simp only [if_pos hxS, if_neg hyS] at hxy
      exact (Finset.disjoint_left.mp hUV (hf.mapsTo hxS)
        (hxy ▸ hg.mapsTo (hy'.resolve_left hyS))).elim
    · simp only [if_neg hxS, if_pos hyS] at hxy
      exact (Finset.disjoint_left.mp hUV (hf.mapsTo hyS)
        (hxy ▸ hg.mapsTo (hx'.resolve_left hxS))).elim
    · simp only [if_neg hxS, if_neg hyS] at hxy
      exact hg.injOn (hx'.resolve_left hxS) (hy'.resolve_left hyS) hxy
  · intro y hy
    have hy' : y ∈ U ∨ y ∈ V := by simpa only [Finset.mem_coe, Finset.mem_union] using hy
    rcases hy' with hyU | hyV
    · obtain ⟨x, hx, heq⟩ := hf.surjOn hyU
      have hxS : x ∈ S := hx
      refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_union]
        exact Or.inl hx
      · simp only [if_pos hxS, heq]
    · obtain ⟨x, hx, heq⟩ := hg.surjOn hyV
      have hxS : x ∉ S := fun hxS => Finset.disjoint_left.mp hST hxS hx
      refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_union]
        exact Or.inr hx
      · simp only [if_neg hxS, heq]

/-- Position domains and displacement sets are glued with their own disjointness proofs. -/
theorem PermutationWithDifferences.glue {S T D E : Finset ℤ} {σ τ : ℤ → ℤ}
    (hσ : PermutationWithDifferences S D σ)
    (hτ : PermutationWithDifferences T E τ)
    (hST : Disjoint S T) (hDE : Disjoint D E) :
    PermutationWithDifferences (S ∪ T) (D ∪ E)
      (fun x => if x ∈ S then σ x else τ x) := by
  constructor
  · exact bijOn_piecewise_union hST hST hσ.1 hτ.1
  · have heq : (fun x => (if x ∈ S then σ x else τ x)-x) =
        (fun x => if x ∈ S then σ x-x else τ x-x) := by
      funext x
      split_ifs <;> rfl
    rw [heq]
    exact bijOn_piecewise_union hST hDE hσ.2 hτ.2

 theorem doubling_with_differences (m : ℤ) (hm : 0 ≤ m) :
    PermutationWithDifferences (Finset.Icc 1 (2*m))
      ((Finset.Icc (-m) m).erase 0) (doubling m) :=
  ⟨doubling_bijOn m hm, doubling_displacement_bijOn m hm⟩


/-- Each pair has two oriented endpoints. -/
def orientedPairs (ps : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × Bool) :=
  ps ×ˢ Finset.univ

 def orientedEndpoint (z : (ℤ × ℤ) × Bool) : ℤ :=
  if z.2 then z.1.2 else z.1.1

 def flipEndpoint (z : (ℤ × ℤ) × Bool) : (ℤ × ℤ) × Bool := (z.1, !z.2)

 theorem orientedEndpoint_image (ps : Finset (ℤ × ℤ)) :
    (orientedPairs ps).image orientedEndpoint = pairEndpoints ps := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨p, b⟩, hz, heq⟩ := Finset.mem_image.mp hx
    have hp : p ∈ ps := (Finset.mem_product.mp hz).1
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, ?_⟩
    cases b <;> simp only [orientedEndpoint, Bool.false_eq_true, ↓reduceIte] at heq
    · exact Finset.mem_insert.mpr (Or.inl heq.symm)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heq.symm))
  · intro hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxp
    rcases hxp with hx | hx
    · exact Finset.mem_image.mpr ⟨(p, false), by simp [orientedPairs, hp], hx.symm⟩
    · exact Finset.mem_image.mpr ⟨(p, true), by simp [orientedPairs, hp], hx.symm⟩

 theorem flipEndpoint_involutive : Function.Involutive flipEndpoint := by
  rintro ⟨p, b⟩
  cases b <;> rfl

 theorem flipEndpoint_bijOn (ps : Finset (ℤ × ℤ)) :
    Set.BijOn flipEndpoint (orientedPairs ps) (orientedPairs ps) := by
  have hmap : Set.MapsTo flipEndpoint (orientedPairs ps) (orientedPairs ps) := by
    intro z hz
    have hp := (Finset.mem_product.mp hz).1
    simp [flipEndpoint, orientedPairs, hp]
  refine ⟨hmap, flipEndpoint_involutive.injective.injOn, ?_⟩
  intro z hz
  exact ⟨flipEndpoint z, hmap hz, flipEndpoint_involutive z⟩

/-- The signed target for a Langford pairing of defect d and largest difference k. -/
def signedDifferences (d k : ℤ) : Finset ℤ :=
  Finset.Icc (-k) (-d) ∪ Finset.Icc d k

 theorem LangfordPairing.orientedDifference_image {d k h : ℤ} {ps : Finset (ℤ × ℤ)}
    (hl : LangfordPairing d k h ps) :
    (orientedPairs ps).image (fun z => orientedEndpoint (flipEndpoint z)-orientedEndpoint z) =
      signedDifferences d k := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨p, b⟩, hz, heq⟩ := Finset.mem_image.mp hx
    have hp : p ∈ ps := (Finset.mem_product.mp hz).1
    have hpd : p.2-p.1 ∈ pairDifferences ps := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [hl.differences] at hpd
    have hpd' := Finset.mem_Icc.mp hpd
    simp only [signedDifferences, Finset.mem_union, Finset.mem_Icc]
    cases b <;> simp only [orientedEndpoint, flipEndpoint, Bool.false_eq_true,
      Bool.not_false, Bool.not_true, ↓reduceIte] at heq <;> omega
  · intro hx
    have hx' : (-k ≤ x ∧ x ≤ -d) ∨ (d ≤ x ∧ x ≤ k) := by
      simpa only [signedDifferences, Finset.mem_union, Finset.mem_Icc] using hx
    rcases hx' with hx' | hx'
    · have hmem : -x ∈ pairDifferences ps := by
        rw [hl.differences]
        exact Finset.mem_Icc.mpr (by omega)
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
      refine Finset.mem_image.mpr ⟨(p, true), by simp [orientedPairs, hp], ?_⟩
      simp only [orientedEndpoint, flipEndpoint, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      omega
    · have hmem : x ∈ pairDifferences ps := by
        rw [hl.differences]
        exact Finset.mem_Icc.mpr hx'
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
      refine Finset.mem_image.mpr ⟨(p, false), by simp [orientedPairs, hp], ?_⟩
      simpa only [orientedEndpoint, flipEndpoint, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte] using heq

 theorem LangfordPairing.endpoint_bijOn {d k h : ℤ} {ps : Finset (ℤ × ℤ)}
    (hl : LangfordPairing d k h ps) :
    Set.BijOn orientedEndpoint (orientedPairs ps)
      ((Finset.Icc 1 (2*(k-d+1)+1)).erase h) := by
  apply (Finset.image_eq_iff_bijOn_of_card ?_).mp
  · exact (orientedEndpoint_image ps).trans hl.endpoints
  · have hm : 0 ≤ k-d+1 := by have := hl.order_nonempty; omega
    have hhm : h ∈ Finset.Icc 1 (2*(k-d+1)+1) := Finset.mem_Icc.mpr hl.hole_mem
    rw [Finset.card_erase_of_mem hhm, Int.card_Icc]
    simp only [orientedPairs, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    have hc := hl.card_le
    omega

 theorem LangfordPairing.orientedDifference_bijOn {d k h : ℤ} {ps : Finset (ℤ × ℤ)}
    (hl : LangfordPairing d k h ps) :
    Set.BijOn (fun z => orientedEndpoint (flipEndpoint z)-orientedEndpoint z)
      (orientedPairs ps) (signedDifferences d k) := by
  apply (Finset.image_eq_iff_bijOn_of_card ?_).mp
  · exact hl.orientedDifference_image
  · have hd := hl.defect_pos
    have hk := hl.order_nonempty
    have hdisj : Disjoint (Finset.Icc (-k) (-d)) (Finset.Icc d k) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      omega
    simp only [signedDifferences, Finset.card_union_of_disjoint hdisj, Int.card_Icc,
      orientedPairs, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    have hc := hl.card_le
    omega

/-- Every checked Langford pairing gives a permutation with exactly its signed differences. -/
theorem LangfordPairing.exists_permutation {d k h : ℤ} {ps : Finset (ℤ × ℤ)}
    (hl : LangfordPairing d k h ps) :
    ∃ σ : ℤ → ℤ, PermutationWithDifferences
      ((Finset.Icc 1 (2*(k-d+1)+1)).erase h) (signedDifferences d k) σ := by
  let e := orientedEndpoint
  let inv := Function.invFunOn e (orientedPairs ps)
  have he := hl.endpoint_bijOn
  have hi : Set.BijOn inv ((Finset.Icc 1 (2*(k-d+1)+1)).erase h) (orientedPairs ps) :=
    Set.BijOn.symm he.invOn_invFunOn.symm he
  let σ : ℤ → ℤ := fun x => orientedEndpoint (flipEndpoint (inv x))
  refine ⟨σ, ?_, ?_⟩
  · exact he.comp ((flipEndpoint_bijOn ps).comp hi)
  · apply (hl.orientedDifference_bijOn.comp hi).congr
    intro x hx
    have heinv : orientedEndpoint (inv x) = x := he.invOn_invFunOn.2 hx
    dsimp only [Function.comp_apply, σ]
    rw [heinv]


/-- Convert a position permutation to the centered hole convention used by signed frames. -/
theorem PermutationWithDifferences.to_centered {k h : ℤ} {σ : ℤ → ℤ}
    (hp : PermutationWithDifferences ((Finset.Icc 1 (2*k+1)).erase h)
      ((Finset.Icc (-k) k).erase 0) σ) :
    DisplacementPermutation k (h-k-1) (fun x => -(k+1)+σ (x-(-(k+1)))) := by
  have ht := hp.translate (-(k+1))
  have heq : (((Finset.Icc 1 (2*k+1)).erase h).image (fun x => -(k+1)+x)) =
      displacementDomain k (h-k-1) := by
    ext x
    simp only [mem_add_image, Finset.mem_erase, Finset.mem_Icc, mem_displacementDomain]
    omega
  rw [heq] at ht
  exact ht

/-- Fill the smaller differences with a doubling prefix before the Langford interval. -/
theorem LangfordPairing.with_doubling_prefix {d k h : ℤ} {ps : Finset (ℤ × ℤ)}
    (hl : LangfordPairing d k h ps) :
    ∃ σ : ℤ → ℤ, PermutationWithDifferences
      ((Finset.Icc 1 (2*k+1)).erase (h+2*(d-1)))
      ((Finset.Icc (-k) k).erase 0) σ := by
  obtain ⟨τ, hτ⟩ := hl.exists_permutation
  have hd := hl.defect_pos
  have hk := hl.order_nonempty
  have hh := hl.hole_mem
  have hp := doubling_with_differences (d-1) (by omega)
  have ht := hτ.translate (2*(d-1))
  have hST : Disjoint (Finset.Icc 1 (2*(d-1)))
      (((Finset.Icc 1 (2*(k-d+1)+1)).erase h).image (fun x => 2*(d-1)+x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx
    simp only [mem_add_image, Finset.mem_erase, Finset.mem_Icc] at hx'
    omega
  have hDE : Disjoint ((Finset.Icc (-(d-1)) (d-1)).erase 0) (signedDifferences d k) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_erase, Finset.mem_Icc] at hx
    simp only [signedDifferences, Finset.mem_union, Finset.mem_Icc] at hx'
    omega
  obtain ⟨σ, hσ⟩ : ∃ σ, PermutationWithDifferences
      (Finset.Icc 1 (2*(d-1)) ∪
        (((Finset.Icc 1 (2*(k-d+1)+1)).erase h).image (fun x => 2*(d-1)+x)))
      (((Finset.Icc (-(d-1)) (d-1)).erase 0) ∪ signedDifferences d k) σ :=
    ⟨_, hp.glue ht hST hDE⟩
  have hS : Finset.Icc 1 (2*(d-1)) ∪
      (((Finset.Icc 1 (2*(k-d+1)+1)).erase h).image (fun x => 2*(d-1)+x)) =
      (Finset.Icc 1 (2*k+1)).erase (h+2*(d-1)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, mem_add_image, Finset.mem_erase]
    omega
  have hD : ((Finset.Icc (-(d-1)) (d-1)).erase 0) ∪ signedDifferences d k =
      (Finset.Icc (-k) k).erase 0 := by
    ext x
    simp only [signedDifferences, Finset.mem_union, Finset.mem_Icc, Finset.mem_erase]
    omega
  exact ⟨σ, hS ▸ hD ▸ hσ⟩

/-- A Langford certificate plus doubling supplies the centered displacement permutation. -/
theorem LangfordPairing.with_doubling_centered {d k h : ℤ} {ps : Finset (ℤ × ℤ)}
    (hl : LangfordPairing d k h ps) :
    ∃ σ : ℤ → ℤ, DisplacementPermutation k (h+2*(d-1)-k-1) σ := by
  obtain ⟨σ, hσ⟩ := hl.with_doubling_prefix
  exact ⟨_, hσ.to_centered⟩


/-- Negating positions negates every displacement. -/
theorem PermutationWithDifferences.negate {S D : Finset ℤ} {σ : ℤ → ℤ}
    (hp : PermutationWithDifferences S D σ) :
    PermutationWithDifferences (S.image (fun x => -x)) (D.image (fun x => -x))
      (fun x => -σ (-x)) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply mem_neg_image.mpr
      simpa only [neg_neg, Finset.mem_coe] using hp.1.mapsTo (mem_neg_image.mp hx)
    · intro x hx y hy hxy
      have heq : σ (-x) = σ (-y) := by dsimp only at hxy; omega
      have he := hp.1.injOn (mem_neg_image.mp hx) (mem_neg_image.mp hy) heq
      omega
    · intro y hy
      obtain ⟨x, hx, heq⟩ := hp.1.surjOn (mem_neg_image.mp hy)
      refine ⟨-x, mem_neg_image.mpr ?_, ?_⟩
      · simpa only [neg_neg, Finset.mem_coe] using hx
      · dsimp only
        rw [neg_neg]
        omega
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply mem_neg_image.mpr
      have hx' := hp.2.mapsTo (mem_neg_image.mp hx)
      have heq : -(-σ (-x)-x) = σ (-x)-(-x) := by ring
      dsimp only
      rw [heq]
      exact hx'
    · intro x hx y hy hxy
      have heq : σ (-x)-(-x) = σ (-y)-(-y) := by dsimp only at hxy; omega
      have he := hp.2.injOn (mem_neg_image.mp hx) (mem_neg_image.mp hy) heq
      omega
    · intro y hy
      obtain ⟨x, hx, heq⟩ := hp.2.surjOn (mem_neg_image.mp hy)
      refine ⟨-x, mem_neg_image.mpr ?_, ?_⟩
      · simpa only [neg_neg, Finset.mem_coe] using hx
      · dsimp only at heq ⊢
        rw [neg_neg]
        omega

/-- Reflection about c/2 reverses positions and the signs of all displacements. -/
theorem PermutationWithDifferences.reflect {S D : Finset ℤ} {σ : ℤ → ℤ}
    (hp : PermutationWithDifferences S D σ) (c : ℤ) :
    PermutationWithDifferences (S.image (fun x => c-x)) (D.image (fun x => -x))
      (fun x => c-σ (c-x)) := by
  have ht := hp.negate.translate c
  simpa only [Finset.image_image, Function.comp_def, ← sub_eq_add_neg, neg_sub] using ht

@[simp] theorem mem_sub_image {S : Finset ℤ} {c x : ℤ} :
    x ∈ S.image (fun y => c-y) ↔ c-x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
    have he : y = c-x := by omega
    simpa only [he] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨c-x, hx, by omega⟩

/-- A full signed displacement set is unchanged by reflecting a position permutation. -/
theorem PermutationWithDifferences.reflect_positions {k h : ℤ} {σ : ℤ → ℤ}
    (hp : PermutationWithDifferences ((Finset.Icc 1 (2*k+1)).erase h)
      ((Finset.Icc (-k) k).erase 0) σ) :
    PermutationWithDifferences ((Finset.Icc 1 (2*k+1)).erase (2*k+2-h))
      ((Finset.Icc (-k) k).erase 0) (fun x => 2*k+2-σ (2*k+2-x)) := by
  have ht := hp.reflect (2*k+2)
  have hS : (((Finset.Icc 1 (2*k+1)).erase h).image (fun x => 2*k+2-x)) =
      (Finset.Icc 1 (2*k+1)).erase (2*k+2-h) := by
    ext x
    simp only [mem_sub_image, Finset.mem_erase, Finset.mem_Icc]
    omega
  have hD : (((Finset.Icc (-k) k).erase 0).image (fun x => -x)) =
      (Finset.Icc (-k) k).erase 0 := by
    ext x
    simp only [mem_neg_image, Finset.mem_erase, Finset.mem_Icc]
    omega
  rw [hS, hD] at ht
  exact ht

end
end GN

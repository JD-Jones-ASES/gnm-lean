import GN.Basic

namespace GN

noncomputable section

/-- An exact partition into three-element sets of sum zero. -/
def ZeroPartition (s : Finset ℤ) (blocks : Finset (Finset ℤ)) : Prop :=
  blocks.biUnion id = s ∧
  (∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c) ∧
  ∀ b ∈ blocks, b.card = 3 ∧ b.sum id = 0

/-- The signed labels used by the critical contraction. -/
def signedVertices (r a : ℤ) : Finset ℤ :=
  Finset.Icc 1 r ∪ ((Finset.Icc 1 (r - 1)).erase a).image (fun x => -x) ∪
    {-(r + a)}

/-- The centered interval with its prescribed hole deleted. -/
def displacementDomain (k j : ℤ) : Finset ℤ := (Finset.Icc (-k) k).erase j

/-- A permutation whose displacements run through the nonzero centered interval. -/
def DisplacementPermutation (k j : ℤ) (σ : ℤ → ℤ) : Prop :=
  Set.BijOn σ (displacementDomain k j) (displacementDomain k j) ∧
  Set.BijOn (fun u => σ u - u) (displacementDomain k j)
    ((Finset.Icc (-k) k).erase 0)

/-- The symmetric interval with zero and the two copies of the hole deleted. -/
def holeVertices (k a : ℤ) : Finset ℤ :=
  (((Finset.Icc (-(3*k+1)) (3*k+1)).erase 0).erase a).erase (-a)

/-- The three residue classes of a displacement triple. -/
def residueTriple (σ : ℤ → ℤ) (u : ℤ) : Finset ℤ :=
  {3*u+1, -(3*σ u+1), 3*(σ u-u)}

 theorem zeroPartition_image {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → Finset ℤ) (hz : ∀ i ∈ u, (f i).card = 3 ∧ (f i).sum id = 0)
    (hd : ∀ i ∈ u, ∀ j ∈ u, i ≠ j → Disjoint (f i) (f j)) :
    ZeroPartition (u.biUnion f) (u.image f) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x; simp
  · intro b hb c hc hbc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact hd i hi j hj (fun h => hbc (congrArg f h))
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact hz i hi

 theorem residueTriple_zero (σ : ℤ → ℤ) (u : ℤ) :
    (residueTriple σ u).card = 3 ∧ (residueTriple σ u).sum id = 0 := by
  have h12 : 3*u+1 ≠ -(3*σ u+1) := by omega
  have h13 : 3*u+1 ≠ 3*(σ u-u) := by omega
  have h23 : -(3*σ u+1) ≠ 3*(σ u-u) := by omega
  have h1 : 3*u+1 ∉ ({-(3*σ u+1), 3*(σ u-u)} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or_intro h12 h13
  have h2 : -(3*σ u+1) ∉ ({3*(σ u-u)} : Finset ℤ) := by
    simpa only [Finset.mem_singleton] using h23
  constructor
  · rw [residueTriple, Finset.card_insert_of_notMem h1,
      Finset.card_insert_of_notMem h2, Finset.card_singleton]
  · rw [residueTriple, Finset.sum_insert h1, Finset.sum_insert h2]
    simp only [Finset.sum_singleton, id_eq]
    ring

 theorem residueTriple_disjoint {k j : ℤ} {σ : ℤ → ℤ}
    (hσ : DisplacementPermutation k j σ) {u v : ℤ}
    (hu : u ∈ displacementDomain k j) (hv : v ∈ displacementDomain k j)
    (huv : u ≠ v) : Disjoint (residueTriple σ u) (residueTriple σ v) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [residueTriple, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with he | he | he
  · exact huv (by omega)
  · omega
  · omega
  · omega
  · exact huv (hσ.1.injOn hu hv (by omega))
  · omega
  · omega
  · omega
  · exact huv (hσ.2.injOn hu hv (by omega))

@[simp] theorem mem_displacementDomain {k j u : ℤ} :
    u ∈ displacementDomain k j ↔ -k ≤ u ∧ u ≤ k ∧ u ≠ j := by
  simp only [displacementDomain, Finset.mem_erase, Finset.mem_Icc]
  tauto

@[simp] theorem mem_holeVertices {k a x : ℤ} :
    x ∈ holeVertices k a ↔
      -(3*k+1) ≤ x ∧ x ≤ 3*k+1 ∧ x ≠ 0 ∧ x ≠ a ∧ x ≠ -a := by
  simp only [holeVertices, Finset.mem_erase, Finset.mem_Icc]
  tauto

/-- The residue triples exhaust exactly the symmetric interval with two holes. -/
 theorem residueTriple_cover {k j a : ℤ} {σ : ℤ → ℤ}
    (ha : a = 3*j+1 ∨ a = -(3*j+1))
    (hσ : DisplacementPermutation k j σ) :
    (displacementDomain k j).biUnion (residueTriple σ) = holeVertices k a := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hx⟩ := Finset.mem_biUnion.mp hx
    have hv := hσ.1.mapsTo hu
    have hd := hσ.2.mapsTo hu
    have hu' := mem_displacementDomain.mp hu
    have hv' := mem_displacementDomain.mp hv
    have hd' : σ u - u ≠ 0 ∧ -k ≤ σ u-u ∧ σ u-u ≤ k := by
      simpa only [Finset.mem_coe, Finset.mem_erase, Finset.mem_Icc] using hd
    rw [mem_holeVertices]
    simp only [residueTriple, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> rcases ha with ha | ha <;> omega
  · intro hx
    have hx' := mem_holeVertices.mp hx
    apply Finset.mem_biUnion.mpr
    by_cases h1 : x % 3 = 1
    · let u := (x-1)/3
      have he : 3*u+1 = x := by dsimp [u]; omega
      have hu : u ∈ displacementDomain k j := by
        rw [mem_displacementDomain]
        rcases ha with ha | ha <;> omega
      refine ⟨u, hu, ?_⟩
      simp only [residueTriple, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl he.symm
    · by_cases h2 : x % 3 = 2
      · let v := (-x-1)/3
        have he : -(3*v+1) = x := by dsimp [v]; omega
        have hv : v ∈ displacementDomain k j := by
          rw [mem_displacementDomain]
          rcases ha with ha | ha <;> omega
        obtain ⟨u, hu, huσ⟩ := hσ.1.surjOn hv
        refine ⟨u, hu, ?_⟩
        simp only [residueTriple, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl (by rw [huσ]; exact he.symm))
      · have he : 3*(x/3) = x := by omega
        have hd : x/3 ∈ (Finset.Icc (-k) k).erase 0 := by
          simp only [Finset.mem_erase, Finset.mem_Icc]
          omega
        obtain ⟨u, hu, huδ⟩ := hσ.2.surjOn hd
        refine ⟨u, hu, ?_⟩
        simp only [residueTriple, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inr (by dsimp only at huδ; omega))

 theorem zeroPartition_hole_of_displacement {k j a : ℤ} {σ : ℤ → ℤ}
    (ha : a = 3*j+1 ∨ a = -(3*j+1))
    (hσ : DisplacementPermutation k j σ) :
    ZeroPartition (holeVertices k a)
      ((displacementDomain k j).image (residueTriple σ)) := by
  rw [← residueTriple_cover ha hσ]
  exact zeroPartition_image _ _ (fun u _ => residueTriple_zero σ u)
    (fun _ hu _ hv huv => residueTriple_disjoint hσ hu hv huv)

 theorem ZeroPartition.subset {s : Finset ℤ} {bs : Finset (Finset ℤ)}
    (h : ZeroPartition s bs) {b : Finset ℤ} (hb : b ∈ bs) : b ⊆ s := by
  intro x hx
  rw [← h.1]
  exact Finset.mem_biUnion.mpr ⟨b, hb, hx⟩

 theorem ZeroPartition.union {s t : Finset ℤ} {bs cs : Finset (Finset ℤ)}
    (hs : ZeroPartition s bs) (ht : ZeroPartition t cs) (hst : Disjoint s t) :
    ZeroPartition (s ∪ t) (bs ∪ cs) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Finset.union_biUnion, hs.1, ht.1]
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

 theorem zeroPartition_single_triple {x y z : ℤ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hs : x+y+z = 0) :
    ZeroPartition {x,y,z} {{x,y,z}} := by
  have h1 : x ∉ ({y,z} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or_intro hxy hxz
  have h2 : y ∉ ({z} : Finset ℤ) := by simpa only [Finset.mem_singleton] using hyz
  refine ⟨by simp, ?_, ?_⟩
  · intro b hb c hc hbc
    simp only [Finset.mem_singleton] at hb hc
    exact (hbc (hb.trans hc.symm)).elim
  · intro b hb
    simp only [Finset.mem_singleton] at hb
    subst b
    constructor
    · rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_singleton]
    · rw [Finset.sum_insert h1, Finset.sum_insert h2]
      simpa only [Finset.sum_singleton, id_eq, add_assoc] using hs

@[simp] theorem mem_neg_image {s : Finset ℤ} {x : ℤ} :
    x ∈ s.image (fun y => -y) ↔ -x ∈ s := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    have hyx : y = -x := by omega
    simpa only [hyx] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨-x, hx, neg_neg x⟩

 theorem hole_union_critical {k a : ℤ} (_hk : 0 ≤ k)
    (ha : 1 ≤ a) (ha' : a ≤ 3*k+1) :
    holeVertices k a ∪ {a, 3*k+2, -(3*k+2+a)} = signedVertices (3*k+2) a := by
  ext x
  simp only [Finset.mem_union, mem_holeVertices, Finset.mem_insert,
    Finset.mem_singleton, signedVertices, mem_neg_image, Finset.mem_erase,
    Finset.mem_Icc]
  omega

/-- A displacement permutation supplies the entire critical signed frame. -/
 theorem zeroPartition_signed_of_displacement {k j a : ℤ} {σ : ℤ → ℤ}
    (hk : 0 ≤ k) (ha : 1 ≤ a) (ha' : a ≤ 3*k+1)
    (haj : a = 3*j+1 ∨ a = -(3*j+1))
    (hσ : DisplacementPermutation k j σ) :
    ∃ bs, ZeroPartition (signedVertices (3*k+2) a) bs := by
  have hh := zeroPartition_hole_of_displacement haj hσ
  have ht := zeroPartition_single_triple
    (x := a) (y := 3*k+2) (z := -(3*k+2+a))
    (by omega) (by omega) (by omega) (by ring)
  have hd : Disjoint (holeVertices k a) {a, 3*k+2, -(3*k+2+a)} := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rw [mem_holeVertices] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    omega
  refine ⟨(displacementDomain k j).image (residueTriple σ) ∪
    {{a, 3*k+2, -(3*k+2+a)}}, ?_⟩
  have h := hh.union ht hd
  rwa [hole_union_critical hk ha ha'] at h

/-- The prescribed nonmultiple of three determines a hole in the centered interval. -/
 theorem exists_residue_hole {k a : ℤ} (hk : 0 ≤ k)
    (ha : 1 ≤ a) (ha' : a ≤ 3*k+1) (ha3 : ¬ (3 : ℤ) ∣ a) :
    ∃ j : ℤ, -k ≤ j ∧ j ≤ k ∧ (a = 3*j+1 ∨ a = -(3*j+1)) := by
  have hn : a % 3 ≠ 0 := by simpa only [Int.dvd_iff_emod_eq_zero] using ha3
  by_cases h1 : a % 3 = 1
  · refine ⟨(a-1)/3, ?_, ?_, Or.inl ?_⟩ <;> omega
  · refine ⟨-(a+1)/3, ?_, ?_, Or.inr ?_⟩ <;> omega

/-- Abstract permutation existence suffices for the critical signed construction. -/
 theorem exists_zeroPartition_signed {k a : ℤ} (hk : 0 ≤ k)
    (ha : 1 ≤ a) (ha' : a ≤ 3*k+1) (ha3 : ¬ (3 : ℤ) ∣ a)
    (hperm : ∀ j : ℤ, -k ≤ j → j ≤ k →
      ∃ σ : ℤ → ℤ, DisplacementPermutation k j σ) :
    ∃ bs, ZeroPartition (signedVertices (3*k+2) a) bs := by
  obtain ⟨j, hj, hj', haj⟩ := exists_residue_hole hk ha ha' ha3
  obtain ⟨σ, hσ⟩ := hperm j hj hj'
  exact zeroPartition_signed_of_displacement hk ha ha' haj hσ

/-- Translation turns a zero triple into a block summing to the next power. -/
 theorem ZeroPartition.shift {s : Finset ℤ} {bs : Finset (Finset ℤ)}
    (h : ZeroPartition s bs) (t : ℕ) :
    GoodOn (s.image (fun x => (3 : ℤ)^t + x))
      (bs.image (fun b => b.image (fun x => (3 : ℤ)^t + x))) := by
  let f : ℤ → ℤ := fun x => (3 : ℤ)^t + x
  have hf : Function.Injective f := by intro x y hxy; dsimp [f] at hxy; omega
  have hg : ∀ b ∈ bs, GoodBlock (b.image f) := by
    intro b hb
    obtain ⟨hc, hz⟩ := h.2.2 b hb
    have hcard : (b.image f).card = 3 := by rw [Finset.card_image_of_injective _ hf, hc]
    refine ⟨Finset.card_pos.mp (by omega), by omega, t+1, ?_⟩
    rw [Finset.sum_image (fun x _ y _ hxy => hf hxy)]
    simp only [f, id_eq]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hc]
    change (3 : ℤ) * 3^t + b.sum id = 3^(t+1)
    rw [hz, add_zero, pow_succ, mul_comm]
  have hd : ∀ b ∈ bs, ∀ c ∈ bs, b ≠ c → Disjoint (b.image f) (c.image f) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro x hx hxc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hxc
    exact Finset.disjoint_left.mp (h.2.1 b hb c hc hbc) hy (by simpa only [hf he] using hz)
  have hh := goodOn_image bs (fun b => b.image f) hg hd
  have hset : bs.biUnion (fun b => b.image f) = s.image f := by
    rw [← h.1]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image]
    aesop
  rwa [hset] at hh

/-- The shift lemma with a separately named power of three. -/
 theorem ZeroPartition.shift_eq {s : Finset ℤ} {bs : Finset (Finset ℤ)}
    (h : ZeroPartition s bs) {P : ℤ} {t : ℕ} (hP : P = (3 : ℤ)^t) :
    GoodOn (s.image (fun x => P+x))
      (bs.image (fun b => b.image (fun x => P+x))) := by
  subst P
  exact h.shift t

end
end GN

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

/-- The signed construction from an abstract low family: a good partition of a subset of the
contracted support whose complement inside that support is already covered by the translated frame
extends, by the singleton of the power and the complement pairs over what is still uncovered, to a
good partition of `{1, …, P + r}`. -/
theorem signedTarget_goodOn {P r a : ℤ} {t : ℕ} {S : Finset ℤ} {L zs : Finset (Finset ℤ)}
    (hP : P = (3 : ℤ) ^ t) (ha : 1 ≤ a) (har : a < r) (hPr : 2 * r < P)
    (hz : ZeroPartition (signedVertices r a) zs) (hL : GoodOn S L)
    (hLsub : S ⊆ criticalSupport r a)
    (hcover : criticalSupport r a ⊆ S ∪ (signedVertices r a).image (fun x => P + x))
    (hdisj : Disjoint S ((signedVertices r a).image (fun x => P + x))) :
    GoodOn (Finset.Icc 1 (P + r))
      (L ∪ shiftBlocks P zs ∪ {{P}} ∪
        ((uncovered P r a L).filter (fun x => 2 * x < P)).image (fun x => {x, P - x})) := by
  have hU : uncovered P r a L
      = Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun x => P + x)) := by
    unfold uncovered
    rw [hL.1]
  have hPpos : 0 < P := by rw [hP]; positivity
  obtain ⟨hf, hhf⟩ : Odd P := by rw [hP]; exact (by decide : Odd (3 : ℤ)).pow
  have hp : P = 2 * hf + 1 := by omega
  have hDbound : ∀ x : ℤ, x ∈ criticalSupport r a → 1 ≤ x ∧ x < P := fun x hx =>
    criticalSupport_bounds ha har hPr hx
  have hTmem : ∀ x : ℤ, x ∈ (signedVertices r a).image (fun y => P + y) ↔
      ((P + 1 ≤ x ∧ x ≤ P + r) ∨ P - x ∈ criticalSupport r a) := fun _ => mem_shift_signed
  have key : ∀ x : ℤ, 1 ≤ x → x < P →
      (x ∈ S ∪ (signedVertices r a).image (fun y => P + y) ↔
        x ∈ criticalSupport r a ∨ P - x ∈ criticalSupport r a) := by
    intro x hx1 hxP
    constructor
    · intro hxm
      rcases Finset.mem_union.mp hxm with hxm | hxm
      · exact Or.inl (hLsub hxm)
      · rcases (hTmem x).mp hxm with hxm | hxm
        · omega
        · exact Or.inr hxm
    · rintro (hxm | hxm)
      · exact hcover hxm
      · exact Finset.mem_union.mpr (Or.inr ((hTmem x).mpr (Or.inr hxm)))
  have hsymm : ∀ x : ℤ, 1 ≤ x → x < P →
      (x ∈ S ∪ (signedVertices r a).image (fun y => P + y) ↔
        P - x ∈ S ∪ (signedVertices r a).image (fun y => P + y)) := by
    intro x hx1 hxP
    rw [key x hx1 hxP, key (P - x) (by omega) (by omega)]
    have hpx : P - (P - x) = x := by ring
    rw [hpx]
    exact or_comm
  have hUmem : ∀ x : ℤ,
      x ∈ Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y)) ↔
        (1 ≤ x ∧ x ≤ P - 1 ∧ x ∉ S ∪ (signedVertices r a).image (fun y => P + y)) := by
    intro x
    simp only [Finset.mem_sdiff, Finset.mem_Icc, and_assoc]
  have hsymmU : ∀ x : ℤ,
      x ∈ Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y)) →
      P - x ∈ Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y)) := by
    intro x hx
    obtain ⟨hx1, hx2, hx3⟩ := (hUmem x).mp hx
    refine (hUmem (P - x)).mpr ⟨by omega, by omega, ?_⟩
    intro hmem
    exact hx3 ((hsymm x hx1 (by omega)).mpr hmem)
  have hpairsupp :
      ((Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y))).filter
          (fun x => 2 * x < P)).biUnion (fun x => ({x, P - x} : Finset ℤ))
        = Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y)) := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨x, ⟨hxU, -⟩, rfl | rfl⟩
      · exact hxU
      · exact hsymmU x hxU
    · intro hy
      obtain ⟨hy1, hy2, -⟩ := (hUmem y).mp hy
      by_cases h2 : 2 * y < P
      · exact ⟨y, ⟨hy, h2⟩, Or.inl rfl⟩
      · exact ⟨P - y, ⟨hsymmU y hy, by omega⟩, Or.inr (by omega)⟩
  have hTgood : GoodOn ((signedVertices r a).image (fun x => P + x)) (shiftBlocks P zs) :=
    hz.shift_eq hP
  have hPblock : GoodOn ({P} : Finset ℤ) ({{P}} : Finset (Finset ℤ)) := by
    have hg : GoodBlock ({P} : Finset ℤ) := by rw [hP]; exact goodBlock_singleton t
    exact hg.goodOn
  have hVgood : GoodOn (Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y)))
      (((Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y))).filter
        (fun x => 2 * x < P)).image (fun x => ({x, P - x} : Finset ℤ))) := by
    have hgood : ∀ x ∈ (Finset.Icc 1 (P - 1) \
        (S ∪ (signedVertices r a).image (fun y => P + y))).filter (fun x => 2 * x < P),
        GoodBlock ({x, P - x} : Finset ℤ) := by
      intro x hx
      obtain ⟨hxU, hx2⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx1, hx1', -⟩ := (hUmem x).mp hxU
      exact goodBlock_pair (by omega) (k := t) (by rw [← hP]; ring)
    have hdisj' : ∀ x ∈ (Finset.Icc 1 (P - 1) \
        (S ∪ (signedVertices r a).image (fun y => P + y))).filter (fun x => 2 * x < P),
        ∀ y ∈ (Finset.Icc 1 (P - 1) \
          (S ∪ (signedVertices r a).image (fun y => P + y))).filter (fun x => 2 * x < P),
        x ≠ y → Disjoint ({x, P - x} : Finset ℤ) ({y, P - y} : Finset ℤ) := by
      intro x hx y hy hxy
      obtain ⟨-, hx2⟩ := Finset.mem_filter.mp hx
      obtain ⟨-, hy2⟩ := Finset.mem_filter.mp hy
      apply Finset.disjoint_left.mpr
      intro z hz1 hz2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
      omega
    have h := goodOn_image _ (fun x => ({x, P - x} : Finset ℤ)) hgood hdisj'
    rwa [hpairsupp] at h
  have hu1 := hL.union hTgood hdisj
  have hd2 : Disjoint (S ∪ (signedVertices r a).image (fun x => P + x)) ({P} : Finset ℤ) := by
    simp only [Finset.disjoint_singleton_right]
    intro hmem
    rcases Finset.mem_union.mp hmem with hm | hm
    · have := hDbound P (hLsub hm)
      omega
    · rcases (hTmem P).mp hm with hm | hm
      · omega
      · have hzero : P - P = 0 := by ring
        rw [hzero] at hm
        have := hDbound 0 hm
        omega
  have hu2 := hu1.union hPblock hd2
  have hd3 : Disjoint (S ∪ (signedVertices r a).image (fun x => P + x) ∪ {P})
      (Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨hx1, hx2, hx3⟩ := (hUmem x).mp hx'
    rcases Finset.mem_union.mp hx with hm | hm
    · exact hx3 hm
    · simp only [Finset.mem_singleton] at hm
      omega
  have hu3 := hu2.union hVgood hd3
  have hsupp : S ∪ (signedVertices r a).image (fun x => P + x) ∪ {P} ∪
      (Finset.Icc 1 (P - 1) \ (S ∪ (signedVertices r a).image (fun y => P + y)))
      = Finset.Icc 1 (P + r) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    constructor
    · rintro (((hm | hm) | hm) | hm)
      · have := hDbound y (hLsub hm)
        omega
      · rcases (hTmem y).mp hm with hm | hm
        · omega
        · have := hDbound (P - y) hm
          omega
      · omega
      · have hm1 := Finset.mem_sdiff.mp hm
        have hm2 := Finset.mem_Icc.mp hm1.1
        omega
    · intro hy
      by_cases hyP : y = P
      · exact Or.inl (Or.inr hyP)
      · by_cases hygt : P < y
        · exact Or.inl (Or.inl (Or.inr ((hTmem y).mpr (Or.inl ⟨by omega, by omega⟩))))
        · by_cases hmem : y ∈ S ∪ (signedVertices r a).image (fun z => P + z)
          · rcases Finset.mem_union.mp hmem with hm | hm
            · exact Or.inl (Or.inl (Or.inl hm))
            · exact Or.inl (Or.inl (Or.inr hm))
          · exact Or.inr ((hUmem y).mpr ⟨by omega, by omega, hmem⟩)
  rw [hU, ← hsupp]
  exact hu3

/-- The frame is recoverable from the signed construction: its translated triples are the only
blocks that sum to three times the power. -/
theorem signedTarget_frame {P r a : ℤ} {t : ℕ} {S : Finset ℤ} {L zs : Finset (Finset ℤ)}
    (hP : P = (3 : ℤ) ^ t) (ha : 1 ≤ a) (har : a < r) (hPr : 2 * r < P)
    (hz : ZeroPartition (signedVertices r a) zs) (hL : GoodOn S L)
    (hLsub : S ⊆ criticalSupport r a) :
    (L ∪ shiftBlocks P zs ∪ {{P}} ∪
        ((uncovered P r a L).filter (fun x => 2 * x < P)).image
          (fun x => {x, P - x})).filter (fun c => c.sum id = 3 * P) = shiftBlocks P zs := by
  have hPpos : 0 < P := by rw [hP]; positivity
  have hDbound : ∀ x : ℤ, x ∈ criticalSupport r a → 1 ≤ x ∧ x < P := fun x hx =>
    criticalSupport_bounds ha har hPr hx
  have hLlt : ∀ c ∈ L, c.sum id < 3 * P := by
    intro c hc
    have hsub : c ⊆ S := hL.subset hc
    have hcard : (c.card : ℤ) ≤ 3 := by exact_mod_cast (hL.block hc).2.1
    have hle : c.sum id ≤ ∑ _x ∈ c, (P - 1) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      have hxb := hDbound x (hLsub (hsub hx))
      simp only [id_eq]
      omega
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    have h1 : (c.card : ℤ) * (P - 1) ≤ 3 * (P - 1) :=
      mul_le_mul_of_nonneg_right hcard (by omega)
    linarith
  have hshift : ∀ c ∈ shiftBlocks P zs, c.sum id = 3 * P := by
    intro c hc
    have hc' : c ∈ zs.image (fun d => d.image (fun x => P + x)) := hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc'
    obtain ⟨hcard, hsum⟩ := hz.2.2 d hd
    exact sum_shift_of_zero hcard hsum
  ext c
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨(((hc | hc) | hc) | hc), hsum⟩
    · exact absurd hsum (by have := hLlt c hc; omega)
    · exact hc
    · simp only [Finset.mem_singleton] at hc
      subst hc
      exact absurd hsum (by simp only [Finset.sum_singleton, id_eq]; omega)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨-, hx2⟩ := Finset.mem_filter.mp hx
      have hne : x ∉ ({P - x} : Finset ℤ) := by
        simp only [Finset.mem_singleton]
        omega
      exact absurd hsum (by
        rw [Finset.sum_insert hne, Finset.sum_singleton]
        simp only [id_eq]
        omega)
  · intro hc
    exact ⟨Or.inl (Or.inl (Or.inr hc)), hshift c hc⟩

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
  have hP' : (P : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hP
  have hPr' : 2 * (r : ℤ) < (P : ℤ) := by exact_mod_cast hPr
  have hab : 1 ≤ a ∧ a ≤ (r : ℤ) := by
    simpa only [interval, Finset.mem_Icc] using hs.subset hb ha
  have haltr : a < (r : ℤ) := by omega
  have hdnot : a + (r : ℤ) ∉ interval r := by
    simp only [interval, Finset.mem_Icc]
    omega
  have hDc : GoodOn (criticalSupport (r : ℤ) a)
      (insert (contractBlock b a (r : ℤ)) (bs.erase b)) := by
    rw [criticalSupport_eq_contractSupport]
    exact hs.contract hb ha hr har hdnot
  have hgoal : GoodOn (Finset.Icc 1 ((P : ℤ) + (r : ℤ))) (targetB (P : ℤ) (r : ℤ) a bs b zs) := by
    unfold targetB
    by_cases hc : (P : ℤ) - ((r : ℤ) + a) ∈ criticalSupport (r : ℤ) a
    · have hLdef : contractedSource (P : ℤ) (r : ℤ) a bs b
          = (insert (contractBlock b a (r : ℤ)) (bs.erase b)).erase
              {(r : ℤ) + a, (P : ℤ) - ((r : ℤ) + a)} := by
        unfold contractedSource
        rw [if_pos hc]
      have hbeq := contractBlock_eq_collision_pair hs hb ha hr har hP' hPr' hc
      have hpairmem : ({(r : ℤ) + a, (P : ℤ) - ((r : ℤ) + a)} : Finset ℤ) ∈
          insert (contractBlock b a (r : ℤ)) (bs.erase b) := by
        rw [← hbeq]
        exact Finset.mem_insert_self _ _
      have hDel := hDc.erase hpairmem
      rw [hLdef]
      refine signedTarget_goodOn hP' hab.1 haltr hPr' hz hDel Finset.sdiff_subset ?_ ?_
      · intro x hx
        by_cases hxp : x ∈ ({(r : ℤ) + a, (P : ℤ) - ((r : ℤ) + a)} : Finset ℤ)
        · refine Finset.mem_union.mpr (Or.inr (mem_shift_signed.mpr (Or.inr ?_)))
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxp
          rcases hxp with rfl | rfl
          · exact hc
          · rw [mem_criticalSupport]
            exact Or.inl (by omega)
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hxp⟩))
      · apply Finset.disjoint_left.mpr
        intro x hx hx'
        have hxL := Finset.mem_sdiff.mp hx
        have hxD := mem_criticalSupport.mp hxL.1
        have hxavoid : x ≠ (r : ℤ) + a ∧ x ≠ (P : ℤ) - ((r : ℤ) + a) := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hxL.2
        rcases mem_shift_signed.mp hx' with hxt | hxt
        · omega
        · rw [mem_criticalSupport] at hxt
          omega
    · have hLdef : contractedSource (P : ℤ) (r : ℤ) a bs b
          = insert (contractBlock b a (r : ℤ)) (bs.erase b) := by
        unfold contractedSource
        rw [if_neg hc]
      rw [hLdef]
      refine signedTarget_goodOn hP' hab.1 haltr hPr' hz hDc (Finset.Subset.refl _) ?_ ?_
      · intro x hx
        exact Finset.mem_union.mpr (Or.inl hx)
      · apply Finset.disjoint_left.mpr
        intro x hx hx'
        rw [mem_criticalSupport] at hx hc
        rcases mem_shift_signed.mp hx' with hxt | hxt
        · omega
        · rw [mem_criticalSupport] at hxt
          omega
  simpa only [interval, Nat.cast_add] using hgoal

/-- The frame can be read back off the signed target: it is the set of blocks summing to `3P`. -/
theorem targetB_frame {P r t : ℕ} {a : ℤ} {bs zs : Finset (Finset ℤ)} {b : Finset ℤ}
    (hP : P = 3 ^ t) (hPr : 2 * r < P) (hs : GoodOn (interval r) bs) (hb : b ∈ bs) (ha : a ∈ b)
    (hr : (r : ℤ) ∈ b) (har : a ≠ (r : ℤ))
    (hz : ZeroPartition (signedVertices (r : ℤ) a) zs) :
    (targetB (P : ℤ) (r : ℤ) a bs b zs).filter (fun c => c.sum id = 3 * (P : ℤ)) =
      shiftBlocks (P : ℤ) zs := by
  have hP' : (P : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hP
  have hPr' : 2 * (r : ℤ) < (P : ℤ) := by exact_mod_cast hPr
  have hab : 1 ≤ a ∧ a ≤ (r : ℤ) := by
    simpa only [interval, Finset.mem_Icc] using hs.subset hb ha
  have haltr : a < (r : ℤ) := by omega
  have hdnot : a + (r : ℤ) ∉ interval r := by
    simp only [interval, Finset.mem_Icc]
    omega
  have hDc : GoodOn (criticalSupport (r : ℤ) a)
      (insert (contractBlock b a (r : ℤ)) (bs.erase b)) := by
    rw [criticalSupport_eq_contractSupport]
    exact hs.contract hb ha hr har hdnot
  unfold targetB
  by_cases hc : (P : ℤ) - ((r : ℤ) + a) ∈ criticalSupport (r : ℤ) a
  · have hLdef : contractedSource (P : ℤ) (r : ℤ) a bs b
        = (insert (contractBlock b a (r : ℤ)) (bs.erase b)).erase
            {(r : ℤ) + a, (P : ℤ) - ((r : ℤ) + a)} := by
      unfold contractedSource
      rw [if_pos hc]
    have hbeq := contractBlock_eq_collision_pair hs hb ha hr har hP' hPr' hc
    have hpairmem : ({(r : ℤ) + a, (P : ℤ) - ((r : ℤ) + a)} : Finset ℤ) ∈
        insert (contractBlock b a (r : ℤ)) (bs.erase b) := by
      rw [← hbeq]
      exact Finset.mem_insert_self _ _
    rw [hLdef]
    exact signedTarget_frame hP' hab.1 haltr hPr' hz (hDc.erase hpairmem) Finset.sdiff_subset
  · have hLdef : contractedSource (P : ℤ) (r : ℤ) a bs b
        = insert (contractBlock b a (r : ℤ)) (bs.erase b) := by
      unfold contractedSource
      rw [if_neg hc]
    rw [hLdef]
    exact signedTarget_frame hP' hab.1 haltr hPr' hz hDc (Finset.Subset.refl _)

/-- Lemma B in counting form: a good partition of `{1, …, r}` with a marked block through `r` and a
partner in that block, together with three signed frames on the vertex set of that partner, give
three good partitions of `{1, …, P + r}`. -/
theorem three_le_count_add_of_source {P r t : ℕ} {a : ℤ} {bs : Finset (Finset ℤ)} {b : Finset ℤ}
    (hP : P = 3 ^ t) (hPr : 2 * r < P) (hs : GoodOn (interval r) bs) (hb : b ∈ bs) (ha : a ∈ b)
    (hr : (r : ℤ) ∈ b) (har : a ≠ (r : ℤ)) (hF : ThreeFrames (r : ℤ) a) : 3 ≤ count (P + r) := by
  obtain ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, h₁₂, h₁₃, h₂₃⟩ := hF
  have hgood : ∀ zs : Finset (Finset ℤ), ZeroPartition (signedVertices (r : ℤ) a) zs →
      IsGoodPartition (P + r) (targetB (P : ℤ) (r : ℤ) a bs b zs) := fun zs hzs =>
    (isGoodPartition_iff _ _).mpr (targetB_goodOn hP hPr hs hb ha hr har hzs)
  have hne : ∀ zs ws : Finset (Finset ℤ), ZeroPartition (signedVertices (r : ℤ) a) zs →
      ZeroPartition (signedVertices (r : ℤ) a) ws → zs ≠ ws →
      targetB (P : ℤ) (r : ℤ) a bs b zs ≠ targetB (P : ℤ) (r : ℤ) a bs b ws := by
    intro zs ws hzs hws hzw heq
    have h1 := targetB_frame hP hPr hs hb ha hr har hzs
    have h2 := targetB_frame hP hPr hs hb ha hr har hws
    rw [heq] at h1
    exact hzw (shiftBlocks_injective (P : ℤ) (h1.symm.trans h2))
  exact three_le_count (hgood _ hz₁) (hgood _ hz₂) (hgood _ hz₃) (hne _ _ hz₁ hz₂ h₁₂)
    (hne _ _ hz₁ hz₃ h₁₃) (hne _ _ hz₂ hz₃ h₂₃)

/-- The critical residue class: three signed frames give three good partitions of `{1, …, P + r}`
for every offset at least eleven congruent to two modulo three. -/
theorem three_le_count_add_of_threeFrames {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hr : 11 ≤ r) (hmod : r % 3 = 2) : 3 ≤ count (P + r) := by
  obtain ⟨bs, hbs⟩ := GN.gurvich_naumova r
  obtain ⟨b, hb, hrb, a, ha, har, ha3⟩ := hbs.maximum_partner (by omega) hmod
  have hab : 1 ≤ a ∧ a ≤ (r : ℤ) := by
    simpa only [interval, Finset.mem_Icc] using hbs.subset hb ha
  have hrZ : (11 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hmodZ : (r : ℤ) % 3 = 2 := by omega
  exact three_le_count_add_of_source hP hPr hbs hb ha hrb har
    (threeFrames_of_mod hrZ hmodZ hab.1 (by omega) ha3)

/-- Offset eight: the unique good partition of `{1, …, 8}` has partner one, and the signed vertex
set of that partner carries three frames. -/
theorem three_le_count_add_eight {P t : ℕ} (hP : P = 3 ^ t) (ht : 3 ≤ t) : 3 ≤ count (P + 8) := by
  have hPr : 2 * 8 < P := by
    have h27 : 3 ^ 3 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    rw [hP]
    norm_num at h27 ⊢
    omega
  exact three_le_count_add_of_source hP hPr GN.smallSource8_good (b := {1, 8}) (a := 1)
    (by simp [GN.smallSource8]) (by simp) (by simp) (by norm_num)
    (by exact_mod_cast threeFrames_eight_one)

end

end GNM

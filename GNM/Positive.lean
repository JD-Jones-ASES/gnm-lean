import GNM.Frames
import GNM.Lift

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

/-- A set with a member that the other set lacks is a different set. -/
private theorem ne_of_mem_of_notMem {α : Type*} [DecidableEq α] {s t : Finset α} {a : α}
    (ha : a ∈ s) (hb : a ∉ t) : s ≠ t := fun h => hb (h ▸ ha)

/-- A set meeting a block of a good partition without being that block is no block of it. -/
private theorem notMem_of_goodOn {s : Finset ℤ} {bs : Finset (Finset ℤ)} (h : GoodOn s bs)
    {b c : Finset ℤ} (hc : c ∈ bs) (hbc : b ≠ c) {x : ℤ} (hxb : x ∈ b) (hxc : x ∈ c) :
    b ∉ bs := fun hb => Finset.disjoint_left.mp (h.2.1 b hb c hc hbc) hxb hxc

/-- Adjoining one good block disjoint from an already partitioned set. -/
private theorem goodOn_insert {s : Finset ℤ} {bs : Finset (Finset ℤ)} {b : Finset ℤ}
    (hb : GoodBlock b) (h : GoodOn s bs) (hd : Disjoint b s) :
    GoodOn (b ∪ s) (insert b bs) := by
  have hu := hb.goodOn.union h hd
  rwa [Finset.insert_eq]

/-- Adjoining three good blocks, each disjoint from everything below it. -/
private theorem goodOn_insert₃ {s : Finset ℤ} {bs : Finset (Finset ℤ)} {b₁ b₂ b₃ : Finset ℤ}
    (hb₁ : GoodBlock b₁) (hb₂ : GoodBlock b₂) (hb₃ : GoodBlock b₃) (h : GoodOn s bs)
    (hd₁ : Disjoint b₁ (b₂ ∪ (b₃ ∪ s))) (hd₂ : Disjoint b₂ (b₃ ∪ s)) (hd₃ : Disjoint b₃ s) :
    GoodOn (b₁ ∪ (b₂ ∪ (b₃ ∪ s))) (insert b₁ (insert b₂ (insert b₃ bs))) :=
  goodOn_insert hb₁ (goodOn_insert hb₂ (goodOn_insert hb₃ h hd₃) hd₂) hd₁

/-- Every element of the vertex set of a symmetric frame lies in the centred interval of its
offset. -/
private theorem frameSet_bounds {r x : ℤ} (hx : x ∈ frameSet r) : -r ≤ x ∧ x ≤ r := by
  have hsub : frameSet r ⊆ Finset.Icc (-r) r := by
    unfold frameSet
    split
    · intro y hy
      exact Finset.mem_of_mem_erase hy
    · exact fun y hy => hy
  simpa only [Finset.mem_Icc] using hsub hx

/-- Translating the vertex set of a symmetric frame by `P` gives the centred interval of the offset
around `P`, with `P` itself removed exactly when three divides the offset. -/
private theorem frameSet_image (P r : ℤ) :
    (frameSet r).image (fun x => P + x) =
      if r % 3 = 0 then (Finset.Icc (P - r) (P + r)).erase P
      else Finset.Icc (P - r) (P + r) := by
  unfold frameSet
  split_ifs with h
  · ext y
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩
      omega
    · intro hy
      exact ⟨y - P, by omega, by omega⟩
  · ext y
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩
      omega
    · intro hy
      exact ⟨y - P, by omega, by omega⟩

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

/-- With the central singleton, the target is the source, the translated frame and that singleton. -/
private theorem targetA_true (P : ℤ) (src zs : Finset (Finset ℤ)) :
    targetA P src zs true = src ∪ shiftBlocks P zs ∪ {{P}} := rfl

/-- Without the central singleton, the target is the source and the translated frame. -/
private theorem targetA_false (P : ℤ) (src zs : Finset (Finset ℤ)) :
    targetA P src zs false = src ∪ shiftBlocks P zs := by
  show src ∪ shiftBlocks P zs ∪ ∅ = src ∪ shiftBlocks P zs
  exact Finset.union_empty _

/-- The symmetric target is a good partition of `{1, …, P + r}`. -/
theorem targetA_goodOn {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) {src zs : Finset (Finset ℤ)}
    (hsrc : GoodOn (interval (P - r - 1)) src) (hz : ZeroPartition (frameSet r) zs) :
    GoodOn (interval (P + r)) (targetA (P : ℤ) src zs (decide (r % 3 = 0))) := by
  have hPZ : (P : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hP
  have hshift : GoodOn ((frameSet (r : ℤ)).image (fun x => (P : ℤ) + x))
      (shiftBlocks (P : ℤ) zs) := hz.shift_eq hPZ
  have hdisj₁ : Disjoint (interval (P - r - 1))
      ((frameSet (r : ℤ)).image (fun x => (P : ℤ) + x)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    simp only [interval, Finset.mem_Icc] at hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx'
    have hb := frameSet_bounds ha
    omega
  have h₁ := hsrc.union hshift hdisj₁
  rcases hmod with hmod | hmod
  · have hmodZ : (r : ℤ) % 3 = 0 := by omega
    have hdec : decide (r % 3 = 0) = true := decide_eq_true hmod
    have hsing : GoodOn ({(P : ℤ)} : Finset ℤ) {{(P : ℤ)}} := by
      rw [hPZ]
      exact (goodBlock_singleton t).goodOn
    have hdisj₂ : Disjoint (interval (P - r - 1) ∪
        (frameSet (r : ℤ)).image (fun x => (P : ℤ) + x)) ({(P : ℤ)} : Finset ℤ) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hx'
      simp only [Finset.mem_singleton] at hx'
      subst hx'
      rcases Finset.mem_union.mp hx with h | h
      · simp only [interval, Finset.mem_Icc] at h
        omega
      · rw [frameSet_image, if_pos hmodZ] at h
        exact (Finset.mem_erase.mp h).1 rfl
    have h₂ := h₁.union hsing hdisj₂
    have hset : interval (P - r - 1) ∪ (frameSet (r : ℤ)).image (fun x => (P : ℤ) + x) ∪
        ({(P : ℤ)} : Finset ℤ) = interval (P + r) := by
      rw [frameSet_image, if_pos hmodZ]
      ext x
      simp only [interval, Finset.mem_union, Finset.mem_Icc, Finset.mem_erase,
        Finset.mem_singleton]
      omega
    rw [hdec, targetA_true, ← hset]
    exact h₂
  · have hmodZ : ¬ ((r : ℤ) % 3 = 0) := by omega
    have hdec : decide (r % 3 = 0) = false := decide_eq_false (by omega)
    have hset : interval (P - r - 1) ∪ (frameSet (r : ℤ)).image (fun x => (P : ℤ) + x)
        = interval (P + r) := by
      rw [frameSet_image, if_neg hmodZ]
      ext x
      simp only [interval, Finset.mem_union, Finset.mem_Icc]
      omega
    rw [hdec, targetA_false, ← hset]
    exact h₁

/-- The frame can be read back off the symmetric target: it is the set of blocks summing to `3P`. -/
theorem targetA_frame {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) {src zs : Finset (Finset ℤ)} {c : Bool}
    (hsrc : GoodOn (interval (P - r - 1)) src) (hz : ZeroPartition (frameSet r) zs) :
    (targetA (P : ℤ) src zs c).filter (fun b => b.sum id = 3 * (P : ℤ)) =
      shiftBlocks (P : ℤ) zs := by
  have hPpos : 0 < (P : ℤ) := by
    have h : 0 < P := by omega
    exact_mod_cast h
  have hsrcsum : ∀ b ∈ src, b.sum id < 3 * (P : ℤ) := by
    intro b hb
    have hsub := hsrc.subset hb
    have hcard : b.card ≤ 3 := (hsrc.block hb).2.1
    have hle : ∀ x ∈ b, id x ≤ (P : ℤ) - (r : ℤ) - 1 := by
      intro x hx
      have hx' := hsub hx
      simp only [interval, Finset.mem_Icc] at hx'
      simp only [id_eq]
      omega
    have hbound := Finset.sum_le_card_nsmul b id ((P : ℤ) - (r : ℤ) - 1) hle
    rw [nsmul_eq_mul] at hbound
    have hcard' : ((b.card : ℕ) : ℤ) ≤ 3 := by exact_mod_cast hcard
    have hnn : (0 : ℤ) ≤ (P : ℤ) - (r : ℤ) - 1 := by omega
    have hmul : ((b.card : ℕ) : ℤ) * ((P : ℤ) - (r : ℤ) - 1) ≤ 3 * ((P : ℤ) - (r : ℤ) - 1) :=
      mul_le_mul_of_nonneg_right hcard' hnn
    have hfin : b.sum id ≤ 3 * ((P : ℤ) - (r : ℤ) - 1) := le_trans hbound hmul
    omega
  have hshiftsum : ∀ b ∈ shiftBlocks (P : ℤ) zs, b.sum id = 3 * (P : ℤ) := by
    intro b hb
    simp only [shiftBlocks, Finset.mem_image] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    obtain ⟨hc₃, hs₀⟩ := hz.2.2 b₀ hb₀
    exact sum_shift_of_zero hc₃ hs₀
  have hextra : ∀ b ∈ (if c then ({{(P : ℤ)}} : Finset (Finset ℤ)) else ∅), b = {(P : ℤ)} := by
    intro b hb
    by_cases hc : c = true
    · rw [hc] at hb
      simpa using hb
    · rw [Bool.not_eq_true] at hc
      rw [hc] at hb
      simp at hb
  ext b
  simp only [Finset.mem_filter, targetA, Finset.mem_union]
  constructor
  · rintro ⟨hb, hsum⟩
    rcases hb with hb | hb
    · rcases hb with hb | hb
      · exact absurd hsum (by have := hsrcsum b hb; omega)
      · exact hb
    · exfalso
      have hbp := hextra b hb
      subst hbp
      rw [Finset.sum_singleton] at hsum
      simp only [id_eq] at hsum
      omega
  · intro hb
    exact ⟨Or.inl (Or.inr hb), hshiftsum b hb⟩

/-- The source can be read back off the symmetric target: it is the set of blocks inside `{1, …, P −
r − 1}`. -/
theorem targetA_src {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) {src zs : Finset (Finset ℤ)} {c : Bool}
    (hsrc : GoodOn (interval (P - r - 1)) src) (hz : ZeroPartition (frameSet r) zs) :
    (targetA (P : ℤ) src zs c).filter (fun b => ∀ x ∈ b, x ≤ (P : ℤ) - r - 1) = src := by
  have hextra : ∀ b ∈ (if c then ({{(P : ℤ)}} : Finset (Finset ℤ)) else ∅), b = {(P : ℤ)} := by
    intro b hb
    by_cases hc : c = true
    · rw [hc] at hb
      simpa using hb
    · rw [Bool.not_eq_true] at hc
      rw [hc] at hb
      simp at hb
  ext b
  simp only [Finset.mem_filter, targetA, Finset.mem_union]
  constructor
  · rintro ⟨hb, hall⟩
    rcases hb with hb | hb
    · rcases hb with hb | hb
      · exact hb
      · exfalso
        simp only [shiftBlocks, Finset.mem_image] at hb
        obtain ⟨b₀, hb₀, hb₀eq⟩ := hb
        obtain ⟨hc₃, _⟩ := hz.2.2 b₀ hb₀
        obtain ⟨y, hy⟩ : b₀.Nonempty := Finset.card_pos.mp (by omega)
        have hmem : (P : ℤ) + y ∈ b := by
          rw [← hb₀eq]
          exact Finset.mem_image_of_mem _ hy
        have hle := hall _ hmem
        have hbd := frameSet_bounds (hz.subset hb₀ hy)
        omega
    · exfalso
      have hbp := hextra b hb
      subst hbp
      have hle := hall (P : ℤ) (Finset.mem_singleton_self _)
      omega
  · intro hb
    refine ⟨Or.inl (Or.inl hb), ?_⟩
    intro x hx
    have hx' := hsrc.subset hb hx
    simp only [interval, Finset.mem_Icc] at hx'
    omega

/-- Two symmetric targets over the same source with different frames are different, because the
frame is the set of blocks summing to `3P`. -/
private theorem targetA_ne_of_frame_ne {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) {src zs ws : Finset (Finset ℤ)} {c : Bool}
    (hsrc : GoodOn (interval (P - r - 1)) src) (hz : ZeroPartition (frameSet r) zs)
    (hw : ZeroPartition (frameSet r) ws) (hne : zs ≠ ws) :
    targetA (P : ℤ) src zs c ≠ targetA (P : ℤ) src ws c := by
  intro heq
  refine hne (shiftBlocks_injective (P : ℤ) ?_)
  have e₁ := targetA_frame (c := c) hP hPr hmod hsrc hz
  have e₂ := targetA_frame (c := c) hP hPr hmod hsrc hw
  rw [← e₁, ← e₂, heq]

/-- Two symmetric targets with different sources are different, because the source is the set of
blocks inside `{1, …, P − r − 1}`. -/
private theorem targetA_ne_of_src_ne {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) {src src' zs ws : Finset (Finset ℤ)} {c : Bool}
    (hsrc : GoodOn (interval (P - r - 1)) src) (hsrc' : GoodOn (interval (P - r - 1)) src')
    (hz : ZeroPartition (frameSet r) zs) (hw : ZeroPartition (frameSet r) ws)
    (hne : src ≠ src') :
    targetA (P : ℤ) src zs c ≠ targetA (P : ℤ) src' ws c := by
  intro heq
  refine hne ?_
  have e₁ := targetA_src (c := c) hP hPr hmod hsrc hz
  have e₂ := targetA_src (c := c) hP hPr hmod hsrc' hw
  rw [← e₁, ← e₂, heq]

/-- Three symmetric frames at an offset congruent to zero or one modulo three give three good
partitions of `{1, …, P + r}`. -/
theorem three_le_count_add_of_threeFrameA {P r t : ℕ} (hP : P = 3 ^ t) (hPr : 2 * r < P)
    (hmod : r % 3 = 0 ∨ r % 3 = 1) (hZ : ThreeFrameA r) : 3 ≤ count (P + r) := by
  obtain ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, h₁₂, h₁₃, h₂₃⟩ := hZ
  obtain ⟨src, hsrc⟩ := GN.gurvich_naumova (P - r - 1)
  exact three_le_count
    ((isGoodPartition_iff _ _).mpr (targetA_goodOn hP hPr hmod hsrc hz₁))
    ((isGoodPartition_iff _ _).mpr (targetA_goodOn hP hPr hmod hsrc hz₂))
    ((isGoodPartition_iff _ _).mpr (targetA_goodOn hP hPr hmod hsrc hz₃))
    (targetA_ne_of_frame_ne hP hPr hmod hsrc hz₁ hz₂ h₁₂)
    (targetA_ne_of_frame_ne hP hPr hmod hsrc hz₁ hz₃ h₁₃)
    (targetA_ne_of_frame_ne hP hPr hmod hsrc hz₂ hz₃ h₂₃)

/-- Offset four: three explicit good partitions of `{1, …, P + 4}` for every power at least
twenty-seven. -/
theorem three_le_count_add_four {P t : ℕ} (hP : P = 3 ^ t) (ht : 3 ≤ t) : 3 ≤ count (P + 4) := by
  sorry

/-- Offset six: the two good partitions of `{1, …, 6}` extended by complement pairs, with the
symmetric frame at `k = 2` and its negation. -/
theorem three_le_count_add_six {P t : ℕ} (hP : P = 3 ^ t) (ht : 3 ≤ t) : 3 ≤ count (P + 6) := by
  have hP27 : 27 ≤ P := by
    subst hP
    have h : (3 : ℕ) ^ 3 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    simpa using h
  have hPZ : (P : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hP
  have hP27Z : (27 : ℤ) ≤ (P : ℤ) := by exact_mod_cast hP27
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (P : ℤ) = 2 * m + 1 := by
    have hodd : Odd ((3 : ℤ) ^ t) := (by decide : Odd (3 : ℤ)).pow
    obtain ⟨u, hu⟩ := hodd
    exact ⟨u, by omega⟩
  -- the complement pairs common to both sources
  have hcp : GoodOn (Finset.Icc (7 : ℤ) ((P : ℤ) - 7)) (canonicalPairs (P : ℤ) 7 m) := by
    have h := canonicalPairs_goodOn (Q := P) (t := t) (lo := (7 : ℤ)) (hi := m) hP (by norm_num)
      (by omega)
    have hset : Finset.Icc (7 : ℤ) m ∪ Finset.Icc ((P : ℤ) - m) ((P : ℤ) - 7)
        = Finset.Icc (7 : ℤ) ((P : ℤ) - 7) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    rwa [hset] at h
  have g126 : GoodBlock ({1, 2, 6} : Finset ℤ) :=
    goodBlock_triple (by norm_num) (by norm_num) (by norm_num) (k := 2) (by norm_num)
  have g3 : GoodBlock ({3} : Finset ℤ) :=
    ⟨Finset.singleton_nonempty _, by simp, 1, by norm_num⟩
  have g45 : GoodBlock ({4, 5} : Finset ℤ) := goodBlock_pair (by norm_num) (k := 2) (by norm_num)
  have g12 : GoodBlock ({1, 2} : Finset ℤ) := goodBlock_pair (by norm_num) (k := 1) (by norm_num)
  have g36 : GoodBlock ({3, 6} : Finset ℤ) := goodBlock_pair (by norm_num) (k := 2) (by norm_num)
  have hsrc₁ : GoodOn (interval (P - 6 - 1))
      (insert ({1, 2, 6} : Finset ℤ) (insert ({3} : Finset ℤ)
        (insert ({4, 5} : Finset ℤ) (canonicalPairs (P : ℤ) 7 m)))) := by
    have h := goodOn_insert₃ g126 g3 g45 hcp
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx'
        omega)
    have hset : ({1, 2, 6} : Finset ℤ) ∪ (({3} : Finset ℤ) ∪
        (({4, 5} : Finset ℤ) ∪ Finset.Icc (7 : ℤ) ((P : ℤ) - 7))) = interval (P - 6 - 1) := by
      ext x
      simp only [interval, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
        Finset.mem_Icc]
      omega
    rwa [hset] at h
  have hsrc₂ : GoodOn (interval (P - 6 - 1))
      (insert ({1, 2} : Finset ℤ) (insert ({3, 6} : Finset ℤ)
        (insert ({4, 5} : Finset ℤ) (canonicalPairs (P : ℤ) 7 m)))) := by
    have h := goodOn_insert₃ g12 g36 g45 hcp
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_Icc] at hx'
        omega)
    have hset : ({1, 2} : Finset ℤ) ∪ (({3, 6} : Finset ℤ) ∪
        (({4, 5} : Finset ℤ) ∪ Finset.Icc (7 : ℤ) ((P : ℤ) - 7))) = interval (P - 6 - 1) := by
      ext x
      simp only [interval, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
        Finset.mem_Icc]
      omega
    rwa [hset] at h
  -- the two sources differ in the block of three
  have hsrcne : (insert ({1, 2, 6} : Finset ℤ) (insert ({3} : Finset ℤ)
      (insert ({4, 5} : Finset ℤ) (canonicalPairs (P : ℤ) 7 m))))
      ≠ (insert ({1, 2} : Finset ℤ) (insert ({3, 6} : Finset ℤ)
      (insert ({4, 5} : Finset ℤ) (canonicalPairs (P : ℤ) 7 m)))) := by
    refine ne_of_mem_of_notMem (a := ({3} : Finset ℤ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) ?_
    refine notMem_of_goodOn hsrc₂ (c := ({3, 6} : Finset ℤ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) ?_
      (Finset.mem_singleton_self _) (Finset.mem_insert_self _ _)
    intro h
    have h6 : (6 : ℤ) ∈ ({3} : Finset ℤ) := by rw [h]; simp
    simp at h6
  -- the symmetric frame at k = 2 and its negation
  have h6cast : ((6 : ℕ) : ℤ) % 3 = 0 := by norm_num
  have hfs : frameSet ((6 : ℕ) : ℤ) = symInterval 2 := by
    unfold frameSet symInterval
    rw [if_pos h6cast]
    norm_num
  have hz₁ : ZeroPartition (frameSet ((6 : ℕ) : ℤ)) (symFamily 2) := by
    rw [hfs]
    exact symFamily_zeroPartition 2 (by norm_num)
  have hz₂ : ZeroPartition (frameSet ((6 : ℕ) : ℤ)) (negBlocks (symFamily 2)) := by
    rw [hfs]
    have h := ZeroPartition.negBlocks (symFamily_zeroPartition 2 (by norm_num))
    rwa [symInterval_neg] at h
  have hzne : symFamily 2 ≠ negBlocks (symFamily 2) := symFamily_ne_neg 2 (by norm_num)
  have hPr : 2 * 6 < P := by omega
  have hmod : 6 % 3 = 0 ∨ 6 % 3 = 1 := Or.inl (by norm_num)
  exact three_le_count
    ((isGoodPartition_iff _ _).mpr (targetA_goodOn hP hPr hmod hsrc₁ hz₁))
    ((isGoodPartition_iff _ _).mpr (targetA_goodOn hP hPr hmod hsrc₁ hz₂))
    ((isGoodPartition_iff _ _).mpr (targetA_goodOn hP hPr hmod hsrc₂ hz₁))
    (targetA_ne_of_frame_ne hP hPr hmod hsrc₁ hz₁ hz₂ hzne)
    (targetA_ne_of_src_ne hP hPr hmod hsrc₁ hsrc₂ hz₁ hz₁ hsrcne)
    (targetA_ne_of_src_ne hP hPr hmod hsrc₁ hsrc₂ hz₂ hz₁ hsrcne)

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

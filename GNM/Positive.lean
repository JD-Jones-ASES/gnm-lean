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
  -- the complement pairs common to all three partitions
  have hcp : GoodOn (Finset.Icc (6 : ℤ) ((P : ℤ) - 6)) (canonicalPairs (P : ℤ) 6 m) := by
    have h := canonicalPairs_goodOn (Q := P) (t := t) (lo := (6 : ℤ)) (hi := m) hP (by norm_num)
      (by omega)
    have hset : Finset.Icc (6 : ℤ) m ∪ Finset.Icc ((P : ℤ) - m) ((P : ℤ) - 6)
        = Finset.Icc (6 : ℤ) ((P : ℤ) - 6) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    rwa [hset] at h
  -- a triple around the power sums to three times it
  have gt : ∀ x y z : ℤ, x ≠ y → x ≠ z → y ≠ z → x + y + z = 3 * (P : ℤ) →
      GoodBlock ({x, y, z} : Finset ℤ) := by
    intro x y z hxy hxz hyz hs
    refine goodBlock_triple hxy hxz hyz (k := t + 1) ?_
    rw [pow_succ, ← hPZ]
    omega
  have gW₁ : GoodBlock ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ) :=
    gt _ _ _ (by omega) (by omega) (by omega) (by ring)
  have gW₂ : GoodBlock ({(P : ℤ) - 3, (P : ℤ) + 1, (P : ℤ) + 2} : Finset ℤ) :=
    gt _ _ _ (by omega) (by omega) (by omega) (by ring)
  have gW₃ : GoodBlock ({(P : ℤ) - 2, (P : ℤ) - 1, (P : ℤ) + 3} : Finset ℤ) :=
    gt _ _ _ (by omega) (by omega) (by omega) (by ring)
  have gV₁ : GoodBlock ({(P : ℤ) - 4, (P : ℤ) + 1, (P : ℤ) + 3} : Finset ℤ) :=
    gt _ _ _ (by omega) (by omega) (by omega) (by ring)
  have gV₂ : GoodBlock ({(P : ℤ) - 3, (P : ℤ) - 1, (P : ℤ) + 4} : Finset ℤ) :=
    gt _ _ _ (by omega) (by omega) (by omega) (by ring)
  have gV₃ : GoodBlock ({(P : ℤ) - 2, (P : ℤ), (P : ℤ) + 2} : Finset ℤ) :=
    gt _ _ _ (by omega) (by omega) (by omega) (by ring)
  have g1 : GoodBlock ({1} : Finset ℤ) :=
    ⟨Finset.singleton_nonempty _, by simp, 0, by norm_num⟩
  have g45 : GoodBlock ({4, 5} : Finset ℤ) := goodBlock_pair (by norm_num) (k := 2) (by norm_num)
  have g234 : GoodBlock ({2, 3, 4} : Finset ℤ) :=
    goodBlock_triple (by norm_num) (by norm_num) (by norm_num) (k := 2) (by norm_num)
  have g23P : GoodBlock ({2, 3, (P : ℤ) - 5} : Finset ℤ) :=
    goodBlock_triple (by norm_num) (by omega) (by omega) (k := t) (by rw [← hPZ]; ring)
  have g5P : GoodBlock ({5, (P : ℤ) - 5} : Finset ℤ) :=
    goodBlock_pair (by omega) (k := t) (by rw [← hPZ]; ring)
  -- the two frames around the power, each covering the centred interval of radius four
  have hU : GoodOn (Finset.Icc ((P : ℤ) - 4) ((P : ℤ) + 4) ∪ Finset.Icc (6 : ℤ) ((P : ℤ) - 6))
      (insert ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ)
        (insert ({(P : ℤ) - 3, (P : ℤ) + 1, (P : ℤ) + 2} : Finset ℤ)
          (insert ({(P : ℤ) - 2, (P : ℤ) - 1, (P : ℤ) + 3} : Finset ℤ)
            (canonicalPairs (P : ℤ) 6 m)))) := by
    have h := goodOn_insert₃ gW₁ gW₂ gW₃ hcp
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
    have hset : ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ) ∪
        (({(P : ℤ) - 3, (P : ℤ) + 1, (P : ℤ) + 2} : Finset ℤ) ∪
          (({(P : ℤ) - 2, (P : ℤ) - 1, (P : ℤ) + 3} : Finset ℤ) ∪
            Finset.Icc (6 : ℤ) ((P : ℤ) - 6)))
        = Finset.Icc ((P : ℤ) - 4) ((P : ℤ) + 4) ∪ Finset.Icc (6 : ℤ) ((P : ℤ) - 6) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_Icc]
      omega
    rwa [hset] at h
  have hV : GoodOn (Finset.Icc ((P : ℤ) - 4) ((P : ℤ) + 4) ∪ Finset.Icc (6 : ℤ) ((P : ℤ) - 6))
      (insert ({(P : ℤ) - 4, (P : ℤ) + 1, (P : ℤ) + 3} : Finset ℤ)
        (insert ({(P : ℤ) - 3, (P : ℤ) - 1, (P : ℤ) + 4} : Finset ℤ)
          (insert ({(P : ℤ) - 2, (P : ℤ), (P : ℤ) + 2} : Finset ℤ)
            (canonicalPairs (P : ℤ) 6 m)))) := by
    have h := goodOn_insert₃ gV₁ gV₂ gV₃ hcp
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
    have hset : ({(P : ℤ) - 4, (P : ℤ) + 1, (P : ℤ) + 3} : Finset ℤ) ∪
        (({(P : ℤ) - 3, (P : ℤ) - 1, (P : ℤ) + 4} : Finset ℤ) ∪
          (({(P : ℤ) - 2, (P : ℤ), (P : ℤ) + 2} : Finset ℤ) ∪
            Finset.Icc (6 : ℤ) ((P : ℤ) - 6)))
        = Finset.Icc ((P : ℤ) - 4) ((P : ℤ) + 4) ∪ Finset.Icc (6 : ℤ) ((P : ℤ) - 6) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_Icc]
      omega
    rwa [hset] at h
  -- the merge block {2, 3, P − 5}, and the split {2, 3, 4}, {5, P − 5}
  have hmerge : ∀ F : Finset (Finset ℤ),
      GoodOn (Finset.Icc ((P : ℤ) - 4) ((P : ℤ) + 4) ∪ Finset.Icc (6 : ℤ) ((P : ℤ) - 6)) F →
      GoodOn (interval (P + 4)) (insert ({1} : Finset ℤ) (insert ({4, 5} : Finset ℤ)
        (insert ({2, 3, (P : ℤ) - 5} : Finset ℤ) F))) := by
    intro F hF
    have h := goodOn_insert₃ g1 g45 g23P hF
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
    have hset : ({1} : Finset ℤ) ∪ (({4, 5} : Finset ℤ) ∪
        (({2, 3, (P : ℤ) - 5} : Finset ℤ) ∪
          (Finset.Icc ((P : ℤ) - 4) ((P : ℤ) + 4) ∪ Finset.Icc (6 : ℤ) ((P : ℤ) - 6))))
        = interval (P + 4) := by
      ext x
      simp only [interval, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
        Finset.mem_Icc]
      omega
    rwa [hset] at h
  have hsplit : ∀ F : Finset (Finset ℤ),
      GoodOn (Finset.Icc ((P : ℤ) - 4) ((P : ℤ) + 4) ∪ Finset.Icc (6 : ℤ) ((P : ℤ) - 6)) F →
      GoodOn (interval (P + 4)) (insert ({1} : Finset ℤ) (insert ({2, 3, 4} : Finset ℤ)
        (insert ({5, (P : ℤ) - 5} : Finset ℤ) F))) := by
    intro F hF
    have h := goodOn_insert₃ g1 g234 g5P hF
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
    have hset : ({1} : Finset ℤ) ∪ (({2, 3, 4} : Finset ℤ) ∪
        (({5, (P : ℤ) - 5} : Finset ℤ) ∪
          (Finset.Icc ((P : ℤ) - 4) ((P : ℤ) + 4) ∪ Finset.Icc (6 : ℤ) ((P : ℤ) - 6))))
        = interval (P + 4) := by
      ext x
      simp only [interval, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
        Finset.mem_Icc]
      omega
    rwa [hset] at h
  have hb₁ := hmerge _ hU
  have hb₂ := hsplit _ hU
  have hb₃ := hsplit _ hV
  -- the first partition carries the merge block, which the other two cannot
  have hmergene : ({2, 3, (P : ℤ) - 5} : Finset ℤ) ≠ ({2, 3, 4} : Finset ℤ) := by
    intro h
    have h4 : (4 : ℤ) ∈ ({2, 3, (P : ℤ) - 5} : Finset ℤ) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    omega
  have h₁₂ : insert ({1} : Finset ℤ) (insert ({4, 5} : Finset ℤ)
      (insert ({2, 3, (P : ℤ) - 5} : Finset ℤ)
        (insert ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ)
          (insert ({(P : ℤ) - 3, (P : ℤ) + 1, (P : ℤ) + 2} : Finset ℤ)
            (insert ({(P : ℤ) - 2, (P : ℤ) - 1, (P : ℤ) + 3} : Finset ℤ)
              (canonicalPairs (P : ℤ) 6 m))))))
      ≠ insert ({1} : Finset ℤ) (insert ({2, 3, 4} : Finset ℤ)
      (insert ({5, (P : ℤ) - 5} : Finset ℤ)
        (insert ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ)
          (insert ({(P : ℤ) - 3, (P : ℤ) + 1, (P : ℤ) + 2} : Finset ℤ)
            (insert ({(P : ℤ) - 2, (P : ℤ) - 1, (P : ℤ) + 3} : Finset ℤ)
              (canonicalPairs (P : ℤ) 6 m)))))) := by
    refine ne_of_mem_of_notMem (a := ({2, 3, (P : ℤ) - 5} : Finset ℤ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) ?_
    exact notMem_of_goodOn hb₂ (c := ({2, 3, 4} : Finset ℤ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hmergene
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
  have h₁₃ : insert ({1} : Finset ℤ) (insert ({4, 5} : Finset ℤ)
      (insert ({2, 3, (P : ℤ) - 5} : Finset ℤ)
        (insert ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ)
          (insert ({(P : ℤ) - 3, (P : ℤ) + 1, (P : ℤ) + 2} : Finset ℤ)
            (insert ({(P : ℤ) - 2, (P : ℤ) - 1, (P : ℤ) + 3} : Finset ℤ)
              (canonicalPairs (P : ℤ) 6 m))))))
      ≠ insert ({1} : Finset ℤ) (insert ({2, 3, 4} : Finset ℤ)
      (insert ({5, (P : ℤ) - 5} : Finset ℤ)
        (insert ({(P : ℤ) - 4, (P : ℤ) + 1, (P : ℤ) + 3} : Finset ℤ)
          (insert ({(P : ℤ) - 3, (P : ℤ) - 1, (P : ℤ) + 4} : Finset ℤ)
            (insert ({(P : ℤ) - 2, (P : ℤ), (P : ℤ) + 2} : Finset ℤ)
              (canonicalPairs (P : ℤ) 6 m)))))) := by
    refine ne_of_mem_of_notMem (a := ({2, 3, (P : ℤ) - 5} : Finset ℤ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) ?_
    exact notMem_of_goodOn hb₃ (c := ({2, 3, 4} : Finset ℤ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hmergene
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
  -- the second and the third differ in the frame around the power
  have hframene : ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ)
      ≠ ({(P : ℤ) - 2, (P : ℤ), (P : ℤ) + 2} : Finset ℤ) := by
    intro h
    have h4 : (P : ℤ) - 4 ∈ ({(P : ℤ) - 2, (P : ℤ), (P : ℤ) + 2} : Finset ℤ) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    omega
  have h₂₃ : insert ({1} : Finset ℤ) (insert ({2, 3, 4} : Finset ℤ)
      (insert ({5, (P : ℤ) - 5} : Finset ℤ)
        (insert ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ)
          (insert ({(P : ℤ) - 3, (P : ℤ) + 1, (P : ℤ) + 2} : Finset ℤ)
            (insert ({(P : ℤ) - 2, (P : ℤ) - 1, (P : ℤ) + 3} : Finset ℤ)
              (canonicalPairs (P : ℤ) 6 m))))))
      ≠ insert ({1} : Finset ℤ) (insert ({2, 3, 4} : Finset ℤ)
      (insert ({5, (P : ℤ) - 5} : Finset ℤ)
        (insert ({(P : ℤ) - 4, (P : ℤ) + 1, (P : ℤ) + 3} : Finset ℤ)
          (insert ({(P : ℤ) - 3, (P : ℤ) - 1, (P : ℤ) + 4} : Finset ℤ)
            (insert ({(P : ℤ) - 2, (P : ℤ), (P : ℤ) + 2} : Finset ℤ)
              (canonicalPairs (P : ℤ) 6 m)))))) := by
    refine ne_of_mem_of_notMem (a := ({(P : ℤ) - 4, (P : ℤ), (P : ℤ) + 4} : Finset ℤ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_self _ _)))) ?_
    exact notMem_of_goodOn hb₃ (c := ({(P : ℤ) - 2, (P : ℤ), (P : ℤ) + 2} : Finset ℤ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))
      hframene (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  exact three_le_count ((isGoodPartition_iff _ _).mpr hb₁) ((isGoodPartition_iff _ _).mpr hb₂)
    ((isGoodPartition_iff _ _).mpr hb₃) h₁₂ h₁₃ h₂₃

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
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
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
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
        omega)
      (by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp at hx hx'
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

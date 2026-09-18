import GNM.Lift

/-!
# The negative offsets

An interval `{1, …, Q − r}` just below a power of three is partitioned by taking a good partition of
`{1, …, r − 1}` and completing it with the canonical pairs `{d, Q − d}`, `r ≤ d ≤ (Q − 1)/2`; the
source is recovered from the target as the blocks lying below `r`, so distinct sources give distinct
targets and the count at `r − 1` is a lower bound for the count at `Q − r`. When `r − 1` is itself
exceptional that route is closed, and two gadgets take its place: one for the offsets just below a
power, where a single canonical pair is merged with the element `Q − R`, and one for the offsets
just above a power, where three pairs are merged.
-/

namespace GNM

open GN

noncomputable section

/-! ### Tools for building and modifying explicit good partitions -/

/-- Every power of three is odd. -/
private theorem pow_three_odd_sub (t : ℕ) : 3 ^ t % 2 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-- A finite family of pairwise disjoint good blocks is a good partition of its union. -/
private theorem goodOn_of_blocks {bs : Finset (Finset ℤ)} (hgood : ∀ b ∈ bs, GoodBlock b)
    (hdisj : ∀ b ∈ bs, ∀ c ∈ bs, b ≠ c → Disjoint b c) : GoodOn (bs.biUnion id) bs :=
  ⟨rfl, hdisj, fun b hb => hgood b hb⟩

/-- Discarding some blocks of a good partition leaves a good partition of what they do not cover. -/
private theorem goodOn_sdiff_blocks {s : Finset ℤ} {bs cs : Finset (Finset ℤ)} (hbs : GoodOn s bs)
    (hsub : cs ⊆ bs) : GoodOn (s \ cs.biUnion id) (bs \ cs) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hb1, hb2⟩ := Finset.mem_sdiff.mp hb
      refine Finset.mem_sdiff.mpr ⟨hbs.subset hb1 hxb, ?_⟩
      intro hmem
      obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.mp hmem
      have hdb : d ≠ b := fun h => hb2 (h ▸ hd)
      exact Finset.disjoint_left.mp (hbs.2.1 d (hsub hd) b hb1 hdb) hxd hxb
    · intro hx
      obtain ⟨hxs, hxc⟩ := Finset.mem_sdiff.mp hx
      rw [← hbs.1] at hxs
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hxs
      refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_sdiff.mpr ⟨hb, ?_⟩, hxb⟩
      intro hbc
      exact hxc (Finset.mem_biUnion.mpr ⟨b, hbc, hxb⟩)
  · intro b hb c hc hbc
    exact hbs.2.1 b (Finset.mem_sdiff.mp hb).1 c (Finset.mem_sdiff.mp hc).1 hbc
  · intro b hb
    exact hbs.block (Finset.mem_sdiff.mp hb).1

/-- Exchanging some blocks of a good partition for another good partition of the set they cover
leaves a good partition of the same set. -/
private theorem goodOn_replace {s : Finset ℤ} {bs ds cs : Finset (Finset ℤ)} (hbs : GoodOn s bs)
    (hsub : ds ⊆ bs) (hcs : GoodOn (ds.biUnion id) cs) : GoodOn s ((bs \ ds) ∪ cs) := by
  have h1 := goodOn_sdiff_blocks hbs hsub
  have h2 := h1.union hcs Finset.sdiff_disjoint
  have hsubs : ds.biUnion id ⊆ s := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
    exact hbs.subset (hsub hb) hxb
  rwa [Finset.sdiff_union_of_subset hsubs] at h2

/-- Two good partitions that put a common element into different blocks are different. -/
private theorem ne_of_block_mem {s : Finset ℤ} {bs cs : Finset (Finset ℤ)} (hcs : GoodOn s cs)
    {b c : Finset ℤ} (hb : b ∈ bs) (hc : c ∈ cs) (x : ℤ) (hxb : x ∈ b) (hxc : x ∈ c)
    (hbc : b ≠ c) : bs ≠ cs := by
  intro h
  rw [h] at hb
  exact Finset.disjoint_left.mp (hcs.2.1 b hb c hc hbc) hxb hxc

/-- A good partition assembled from the complementary pairs `{j, R − j}` over a set of deficits
together with finitely many further blocks. -/
private theorem goodOn_pairs_union {R sR : ℕ} (hR : R = 3 ^ sR) {J : Finset ℤ}
    {E : Finset (Finset ℤ)} {s : Finset ℤ}
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ 2 * j < (R : ℤ))
    (hE : ∀ b ∈ E, GoodBlock b)
    (hEE : ∀ b ∈ E, ∀ c ∈ E, b ≠ c → Disjoint b c)
    (hJE : ∀ j ∈ J, ∀ b ∈ E, Disjoint ({j, (R : ℤ) - j} : Finset ℤ) b)
    (hcov : J.biUnion (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪ E.biUnion id = s) :
    GoodOn s (J.image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪ E) := by
  have hRz : (R : ℤ) = (3 : ℤ) ^ sR := by exact_mod_cast hR
  refine ⟨?_, ?_, ?_⟩
  · simp only [Finset.union_biUnion, Finset.image_biUnion, id_eq]
    exact hcov
  · intro b hb c hc hbc
    simp only [Finset.mem_union, Finset.mem_image] at hb hc
    rcases hb with ⟨j, hj, rfl⟩ | hb
    · rcases hc with ⟨k, hk, rfl⟩ | hc
      · have hjk : j ≠ k := fun h => hbc (by rw [h])
        obtain ⟨hj1, hj2⟩ := hJ j hj
        obtain ⟨hk1, hk2⟩ := hJ k hk
        apply Finset.disjoint_left.mpr
        intro y hy hy'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
        omega
      · exact hJE j hj c hc
    · rcases hc with ⟨k, hk, rfl⟩ | hc
      · exact (hJE k hk b hb).symm
      · exact hEE b hb c hc hbc
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_image] at hb
    rcases hb with ⟨j, hj, rfl⟩ | hb
    · obtain ⟨hj1, hj2⟩ := hJ j hj
      exact goodBlock_pair (by omega) (k := sR) (by rw [← hRz]; ring)
    · exact hE b hb

/-! ### Lemma C -/

/-- The negative target: a partition of `{1, …, r − 1}` and the canonical pairs above `r`. -/
def targetC (Q r : ℤ) (src : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  src ∪ canonicalPairs Q r ((Q - 1) / 2)

/-- The negative target is a good partition of `{1, …, Q − r}`. -/
theorem targetC_goodOn {Q r t : ℕ} (hQ : Q = 3 ^ t) (hr : 1 ≤ r) (hQr : 2 * r < Q)
    {src : Finset (Finset ℤ)} (hsrc : GoodOn (interval (r - 1)) src) :
    GoodOn (interval (Q - r)) (targetC (Q : ℤ) (r : ℤ) src) := by
  have hodd : Q % 2 = 1 := by rw [hQ]; exact pow_three_odd_sub t
  have hhalf : 2 * (((Q : ℤ) - 1) / 2) = (Q : ℤ) - 1 := by omega
  have hcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  have hcast' : ((Q - r : ℕ) : ℤ) = (Q : ℤ) - (r : ℤ) := by omega
  have hcan := canonicalPairs_goodOn (Q := Q) (t := t) (lo := (r : ℤ))
    (hi := ((Q : ℤ) - 1) / 2) hQ (by exact_mod_cast hr) (by omega)
  have hdisj : Disjoint (interval (r - 1))
      (Finset.Icc (r : ℤ) (((Q : ℤ) - 1) / 2) ∪
        Finset.Icc ((Q : ℤ) - ((Q : ℤ) - 1) / 2) ((Q : ℤ) - (r : ℤ))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [interval, Finset.mem_Icc, Finset.mem_union] at hx hx'
    omega
  have hun := hsrc.union hcan hdisj
  have hset : interval (r - 1) ∪
      (Finset.Icc (r : ℤ) (((Q : ℤ) - 1) / 2) ∪
        Finset.Icc ((Q : ℤ) - ((Q : ℤ) - 1) / 2) ((Q : ℤ) - (r : ℤ))) = interval (Q - r) := by
    ext x
    simp only [interval, Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hset] at hun
  exact hun

/-- The source can be read back off the negative target: it is the set of blocks below `r`. -/
theorem targetC_src {Q r t : ℕ} (hQ : Q = 3 ^ t) (hr : 1 ≤ r) (hQr : 2 * r < Q)
    {src : Finset (Finset ℤ)} (hsrc : GoodOn (interval (r - 1)) src) :
    (targetC (Q : ℤ) (r : ℤ) src).filter (fun b => ∀ x ∈ b, x < (r : ℤ)) = src := by
  have hodd : Q % 2 = 1 := by rw [hQ]; exact pow_three_odd_sub t
  have hhalf : 2 * (((Q : ℤ) - 1) / 2) = (Q : ℤ) - 1 := by omega
  have hcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  ext b
  simp only [targetC, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hb | hb, hlow⟩
    · exact hb
    · rw [canonicalPairs] at hb
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
      exfalso
      have hlt := hlow ((Q : ℤ) - d) (by simp)
      omega
  · intro hb
    refine ⟨Or.inl hb, fun x hx => ?_⟩
    have hxs := hsrc.subset hb hx
    simp only [interval, Finset.mem_Icc] at hxs
    omega

/-- The count at `r − 1` bounds the count at `Q − r`. -/
theorem count_pred_le_count_sub {Q r t : ℕ} (hQ : Q = 3 ^ t) (hr : 1 ≤ r) (hQr : 2 * r < Q) :
    count (r - 1) ≤ count (Q - r) := by
  refine count_le_of_injOn (targetC (Q : ℤ) (r : ℤ)) (fun bs hbs => ?_) (fun bs cs hbs hcs h => ?_)
  · rw [isGoodPartition_iff] at hbs ⊢
    exact targetC_goodOn hQ hr hQr hbs
  · rw [isGoodPartition_iff] at hbs hcs
    rw [← targetC_src hQ hr hQr hbs, ← targetC_src hQ hr hQr hcs, h]

/-! ### Explicit sources just above a power of three -/

/-- Just above a power of three `R ≥ 81` there is, for each of the five offsets `δ` for which
`R + δ` is exceptional, a good partition of `{1, …, R + δ − 1}` containing every complementary pair
`{j, R − j}` with `4 ≤ j`, `2j < R` and `j ≠ 9`. -/
private theorem srcAbove_exists {R s δ : ℕ} (hR : R = 3 ^ s) (hs : 4 ≤ s)
    (hδ : δ = 1 ∨ δ = 2 ∨ δ = 3 ∨ δ = 4 ∨ δ = 6) :
    ∃ src : Finset (Finset ℤ), GoodOn (interval (R + δ - 1)) src ∧
      ∀ j : ℤ, 4 ≤ j → 2 * j < (R : ℤ) → j ≠ 9 → ({j, (R : ℤ) - j} : Finset ℤ) ∈ src := by
  have hR81 : 81 ≤ R := by
    rw [hR]
    calc (81 : ℕ) = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hRz : (R : ℤ) = (3 : ℤ) ^ s := by exact_mod_cast hR
  have hRodd : R % 2 = 1 := by rw [hR]; exact pow_three_odd_sub s
  obtain ⟨a, haR⟩ : ∃ a : ℤ, (R : ℤ) = 2 * a + 1 := ⟨((R : ℤ) - 1) / 2, by omega⟩
  have ha40 : 40 ≤ a := by omega
  have hb1 : GoodBlock ({(1 : ℤ)} : Finset ℤ) := ⟨by simp, by simp, 0, by norm_num⟩
  have hb3 : GoodBlock ({(3 : ℤ)} : Finset ℤ) := ⟨by simp, by simp, 1, by norm_num⟩
  have hb9 : GoodBlock ({(9 : ℤ)} : Finset ℤ) := ⟨by simp, by simp, 2, by norm_num⟩
  have hbR : GoodBlock ({(R : ℤ)} : Finset ℤ) := ⟨by simp, by simp, s, by simpa using hRz⟩
  have hb12 : GoodBlock ({(1 : ℤ), 2} : Finset ℤ) :=
    goodBlock_pair (by norm_num) (k := 1) (by norm_num)
  have htriple : ∀ x y z : ℤ, x ≠ y → x ≠ z → y ≠ z → x + y + z = 3 * (R : ℤ) →
      GoodBlock ({x, y, z} : Finset ℤ) := by
    intro x y z h1 h2 h3 hsum
    refine goodBlock_triple h1 h2 h3 (k := s + 1) ?_
    rw [pow_succ, ← hRz]
    linarith
  rcases hδ with rfl | rfl | rfl | rfl | rfl
  · -- the pairs `{j, R − j}` and the singleton `{R}`
    refine ⟨(Finset.Icc (1 : ℤ) a).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪
      {{(R : ℤ)}}, ?_, ?_⟩
    · apply goodOn_pairs_union hR
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        omega
      · intro X hX
        simp only [Finset.mem_singleton] at hX
        subst hX
        exact hbR
      · intro X hX Y hY hXY
        simp only [Finset.mem_singleton] at hX hY
        subst hX
        subst hY
        exact absurd rfl hXY
      · intro j hj X hX
        simp only [Finset.mem_Icc] at hj
        simp only [Finset.mem_singleton] at hX
        subst hX
        apply Finset.disjoint_left.mpr
        intro x hx hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        omega
      · simp only [Finset.singleton_biUnion, id_eq]
        ext x
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, interval]
        constructor
        · rintro (⟨j, hj, hx⟩ | hx) <;> omega
        · intro hx
          by_cases h1 : 1 ≤ x ∧ x ≤ a
          · exact Or.inl ⟨x, by omega, Or.inl rfl⟩
          · by_cases h2 : a + 1 ≤ x ∧ x ≤ (R : ℤ) - 1
            · exact Or.inl ⟨(R : ℤ) - x, by omega, Or.inr (by omega)⟩
            · exact Or.inr (by omega)
    · intro j h4 h2j h9
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, ?_, rfl⟩))
      simp only [Finset.mem_Icc]
      omega
  · -- the pairs from two on, `{1}` and `{R − 1, R, R + 1}`
    refine ⟨(Finset.Icc (2 : ℤ) a).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪
      {{(1 : ℤ)}, {(R : ℤ) - 1, (R : ℤ), (R : ℤ) + 1}}, ?_, ?_⟩
    · apply goodOn_pairs_union hR
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        omega
      · intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact hb1
        · exact htriple _ _ _ (by omega) (by omega) (by omega) (by omega)
      · intro X hX Y hY hXY
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;>
          first
            | exact absurd rfl hXY
            | omega
      · intro j hj X hX
        simp only [Finset.mem_Icc] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rcases hX with rfl | rfl <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;> omega
      · simp only [Finset.biUnion_insert, Finset.singleton_biUnion, id_eq]
        ext x
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, interval]
        constructor
        · rintro (⟨j, hj, hx⟩ | hx) <;> omega
        · intro hx
          by_cases h1 : 2 ≤ x ∧ x ≤ a
          · exact Or.inl ⟨x, by omega, Or.inl rfl⟩
          · by_cases h2 : a + 1 ≤ x ∧ x ≤ (R : ℤ) - 2
            · exact Or.inl ⟨(R : ℤ) - x, by omega, Or.inr (by omega)⟩
            · exact Or.inr (by omega)
    · intro j h4 h2j h9
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, ?_, rfl⟩))
      simp only [Finset.mem_Icc]
      omega
  · -- the pairs except at three, `{3}`, `{R}` and `{R − 3, R + 1, R + 2}`
    refine ⟨(Finset.Icc (1 : ℤ) a \ {3}).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪
      {{(3 : ℤ)}, {(R : ℤ)}, {(R : ℤ) - 3, (R : ℤ) + 1, (R : ℤ) + 2}}, ?_, ?_⟩
    · apply goodOn_pairs_union hR
      · intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton] at hj
        omega
      · intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl | rfl
        · exact hb3
        · exact hbR
        · exact htriple _ _ _ (by omega) (by omega) (by omega) (by omega)
      · intro X hX Y hY hXY
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;>
          first
            | exact absurd rfl hXY
            | omega
      · intro j hj X hX
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rcases hX with rfl | rfl | rfl <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;> omega
      · simp only [Finset.biUnion_insert, Finset.singleton_biUnion, id_eq]
        ext x
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_Icc,
          Finset.mem_insert, Finset.mem_singleton, interval]
        constructor
        · rintro (⟨j, hj, hx⟩ | hx) <;> omega
        · intro hx
          by_cases h1 : 1 ≤ x ∧ x ≤ a ∧ x ≠ 3
          · exact Or.inl ⟨x, by omega, Or.inl rfl⟩
          · by_cases h2 : a + 1 ≤ x ∧ x ≤ (R : ℤ) - 1 ∧ x ≠ (R : ℤ) - 3
            · exact Or.inl ⟨(R : ℤ) - x, by omega, Or.inr (by omega)⟩
            · exact Or.inr (by omega)
    · intro j h4 h2j h9
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, ?_, rfl⟩))
      simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
      omega
  · -- the pairs from four on, and five further blocks
    refine ⟨(Finset.Icc (4 : ℤ) a).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪
      {{(1 : ℤ), 2}, {(3 : ℤ)}, {(R : ℤ)}, {(R : ℤ) - 3, (R : ℤ) + 1, (R : ℤ) + 2},
        {(R : ℤ) - 2, (R : ℤ) - 1, (R : ℤ) + 3}}, ?_, ?_⟩
    · apply goodOn_pairs_union hR
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        omega
      · intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl | rfl | rfl | rfl
        · exact hb12
        · exact hb3
        · exact hbR
        · exact htriple _ _ _ (by omega) (by omega) (by omega) (by omega)
        · exact htriple _ _ _ (by omega) (by omega) (by omega) (by omega)
      · intro X hX Y hY hXY
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rcases hX with rfl | rfl | rfl | rfl | rfl <;>
          rcases hY with rfl | rfl | rfl | rfl | rfl <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;>
          first
            | exact absurd rfl hXY
            | omega
      · intro j hj X hX
        simp only [Finset.mem_Icc] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rcases hX with rfl | rfl | rfl | rfl | rfl <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;> omega
      · simp only [Finset.biUnion_insert, Finset.singleton_biUnion, id_eq]
        ext x
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, interval]
        constructor
        · rintro (⟨j, hj, hx⟩ | hx) <;> omega
        · intro hx
          by_cases h1 : 4 ≤ x ∧ x ≤ a
          · exact Or.inl ⟨x, by omega, Or.inl rfl⟩
          · by_cases h2 : a + 1 ≤ x ∧ x ≤ (R : ℤ) - 4
            · exact Or.inl ⟨(R : ℤ) - x, by omega, Or.inr (by omega)⟩
            · exact Or.inr (by omega)
    · intro j h4 h2j h9
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, ?_, rfl⟩))
      simp only [Finset.mem_Icc]
      omega
  · -- the pairs from four on except at nine, and seven further blocks
    refine ⟨(Finset.Icc (4 : ℤ) a \ {9}).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪
      {{(1 : ℤ), 2}, {(3 : ℤ)}, {(9 : ℤ)}, {(R : ℤ)},
        {(R : ℤ) - 9, (R : ℤ) + 4, (R : ℤ) + 5}, {(R : ℤ) - 3, (R : ℤ) + 1, (R : ℤ) + 2},
        {(R : ℤ) - 2, (R : ℤ) - 1, (R : ℤ) + 3}}, ?_, ?_⟩
    · apply goodOn_pairs_union hR
      · intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton] at hj
        omega
      · intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hb12
        · exact hb3
        · exact hb9
        · exact hbR
        · exact htriple _ _ _ (by omega) (by omega) (by omega) (by omega)
        · exact htriple _ _ _ (by omega) (by omega) (by omega) (by omega)
        · exact htriple _ _ _ (by omega) (by omega) (by omega) (by omega)
      · intro X hX Y hY hXY
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;>
          first
            | exact absurd rfl hXY
            | omega
      · intro j hj X hX
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        apply Finset.disjoint_left.mpr
        intro x hx hy
        rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;> omega
      · simp only [Finset.biUnion_insert, Finset.singleton_biUnion, id_eq]
        ext x
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_Icc,
          Finset.mem_insert, Finset.mem_singleton, interval]
        constructor
        · rintro (⟨j, hj, hx⟩ | hx) <;> omega
        · intro hx
          by_cases h1 : 4 ≤ x ∧ x ≤ a ∧ x ≠ 9
          · exact Or.inl ⟨x, by omega, Or.inl rfl⟩
          · by_cases h2 : a + 1 ≤ x ∧ x ≤ (R : ℤ) - 4 ∧ x ≠ (R : ℤ) - 9
            · exact Or.inl ⟨(R : ℤ) - x, by omega, Or.inr (by omega)⟩
            · exact Or.inr (by omega)
    · intro j h4 h2j h9
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, ?_, rfl⟩))
      simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
      omega

/-! ### The two gadgets -/

/-- The first gadget: for an offset `R − e + 1` just below a power `R`, the canonical completion and
the two single merges of a canonical pair with the element `Q − R` give three good partitions. -/
theorem three_le_count_sub_below {Q R e t s : ℕ} (hR : R = 3 ^ s) (hs : 3 ≤ s)
    (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) (hQ : Q = 3 ^ t) (hQR : 3 * R ≤ Q) :
    3 ≤ count (Q - (R - e + 1)) := by
  have he1 : 1 ≤ e ∧ e ≤ 6 := by omega
  have hR27 : 27 ≤ R := by
    rw [hR]
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hRz : (R : ℤ) = (3 : ℤ) ^ s := by exact_mod_cast hR
  have hQz : (Q : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hQ
  have hRodd : R % 2 = 1 := by rw [hR]; exact pow_three_odd_sub s
  obtain ⟨a, haR⟩ : ∃ a : ℤ, (R : ℤ) = 2 * a + 1 := ⟨((R : ℤ) - 1) / 2, by omega⟩
  have ha13 : 13 ≤ a := by omega
  have hbR : GoodBlock ({(R : ℤ)} : Finset ℤ) := ⟨by simp, by simp, s, by simpa using hRz⟩
  obtain ⟨small, hsmall⟩ := GN.gurvich_naumova (e - 1)
  have hsrcC : GoodOn (interval (R - e))
      ((Finset.Icc (e : ℤ) a).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪ small) := by
    apply goodOn_pairs_union hR
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      omega
    · intro X hX
      exact hsmall.block hX
    · exact hsmall.2.1
    · intro j hj X hX
      simp only [Finset.mem_Icc] at hj
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hxi := hsmall.subset hX hy
      simp only [interval, Finset.mem_Icc] at hxi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    · rw [hsmall.1]
      ext x
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton, interval]
      constructor
      · rintro (⟨j, hj, hx⟩ | hx) <;> omega
      · intro hx
        by_cases h1 : (e : ℤ) ≤ x ∧ x ≤ a
        · exact Or.inl ⟨x, by omega, Or.inl rfl⟩
        · by_cases h2 : a + 1 ≤ x ∧ x ≤ (R : ℤ) - (e : ℤ)
          · exact Or.inl ⟨(R : ℤ) - x, by omega, Or.inr (by omega)⟩
          · exact Or.inr (by omega)
  have hsrc' : GoodOn (interval (R - e + 1 - 1))
      ((Finset.Icc (e : ℤ) a).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪ small) := by
    have h : R - e + 1 - 1 = R - e := by omega
    rw [h]
    exact hsrcC
  obtain ⟨T₀, hT0def⟩ : ∃ X, X = targetC (Q : ℤ) ((R - e + 1 : ℕ) : ℤ)
      ((Finset.Icc (e : ℤ) a).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪ small) := ⟨_, rfl⟩
  have hT0 : GoodOn (interval (Q - (R - e + 1))) T₀ := by
    rw [hT0def]
    exact targetC_goodOn hQ (by omega) (by omega) hsrc'
  have hmemsrc : ∀ X ∈ (Finset.Icc (e : ℤ) a).image (fun j => ({j, (R : ℤ) - j} : Finset ℤ)) ∪
      small, X ∈ T₀ := by
    intro X hX
    rw [hT0def]
    simp only [targetC]
    exact Finset.mem_union.mpr (Or.inl hX)
  have hmemcan : ∀ d : ℤ, ((R - e + 1 : ℕ) : ℤ) ≤ d → 2 * d < (Q : ℤ) →
      ({d, (Q : ℤ) - d} : Finset ℤ) ∈ T₀ := by
    intro d h1 h2
    rw [hT0def]
    simp only [targetC, canonicalPairs]
    refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨d, ?_, rfl⟩))
    simp only [Finset.mem_Icc]
    omega
  have hRQ : ({(R : ℤ), (Q : ℤ) - (R : ℤ)} : Finset ℤ) ∈ T₀ :=
    hmemcan (R : ℤ) (by omega) (by omega)
  have key : ∀ j : ℤ, (e : ℤ) ≤ j → j ≤ (e : ℤ) + 1 → ∃ T : Finset (Finset ℤ),
      GoodOn (interval (Q - (R - e + 1))) T ∧
        ({j, (R : ℤ) - j, (Q : ℤ) - (R : ℤ)} : Finset ℤ) ∈ T := by
    intro j hj1 hj2
    refine ⟨(T₀ \ {{j, (R : ℤ) - j}, {(R : ℤ), (Q : ℤ) - (R : ℤ)}}) ∪
      {{j, (R : ℤ) - j, (Q : ℤ) - (R : ℤ)}, {(R : ℤ)}}, ?_, ?_⟩
    · refine goodOn_replace hT0 ?_ ?_
      · intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact hmemsrc _ (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
            ⟨j, Finset.mem_Icc.mpr ⟨hj1, by omega⟩, rfl⟩)))
        · exact hRQ
      · have hCgood : GoodOn
            (({{j, (R : ℤ) - j, (Q : ℤ) - (R : ℤ)}, {(R : ℤ)}} : Finset (Finset ℤ)).biUnion id)
            ({{j, (R : ℤ) - j, (Q : ℤ) - (R : ℤ)}, {(R : ℤ)}} : Finset (Finset ℤ)) := by
          apply goodOn_of_blocks
          · intro X hX
            simp only [Finset.mem_insert, Finset.mem_singleton] at hX
            rcases hX with rfl | rfl
            · exact goodBlock_triple (by omega) (by omega) (by omega) (k := t)
                (by rw [← hQz]; omega)
            · exact hbR
          · intro X hX Y hY hXY
            simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
            apply Finset.disjoint_left.mpr
            intro x hx hy
            rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;>
              first
                | exact absurd rfl hXY
                | omega
        have hsupp : ({{j, (R : ℤ) - j, (Q : ℤ) - (R : ℤ)}, {(R : ℤ)}} :
              Finset (Finset ℤ)).biUnion id =
            ({{j, (R : ℤ) - j}, {(R : ℤ), (Q : ℤ) - (R : ℤ)}} : Finset (Finset ℤ)).biUnion id := by
          simp only [Finset.biUnion_insert, Finset.singleton_biUnion, id_eq]
          ext x
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          omega
        rw [hsupp] at hCgood
        exact hCgood
    · exact Finset.mem_union.mpr (Or.inr (by simp))
  obtain ⟨T₁, hT1, hT1mem⟩ := key (e : ℤ) (by omega) (by omega)
  obtain ⟨T₂, hT2, hT2mem⟩ := key ((e : ℤ) + 1) (by omega) (by omega)
  have hne01 : T₀ ≠ T₁ := by
    refine ne_of_block_mem hT1 hRQ hT1mem ((Q : ℤ) - (R : ℤ)) (by simp) (by simp) ?_
    intro h
    have hmem : (e : ℤ) ∈ ({(R : ℤ), (Q : ℤ) - (R : ℤ)} : Finset ℤ) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hne02 : T₀ ≠ T₂ := by
    refine ne_of_block_mem hT2 hRQ hT2mem ((Q : ℤ) - (R : ℤ)) (by simp) (by simp) ?_
    intro h
    have hmem : (e : ℤ) + 1 ∈ ({(R : ℤ), (Q : ℤ) - (R : ℤ)} : Finset ℤ) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hne12 : T₁ ≠ T₂ := by
    refine ne_of_block_mem hT2 hT1mem hT2mem ((Q : ℤ) - (R : ℤ)) (by simp) (by simp) ?_
    intro h
    have hmem : (e : ℤ) ∈
        ({(e : ℤ) + 1, (R : ℤ) - ((e : ℤ) + 1), (Q : ℤ) - (R : ℤ)} : Finset ℤ) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  exact three_le_count ((isGoodPartition_iff _ _).mpr hT0) ((isGoodPartition_iff _ _).mpr hT1)
    ((isGoodPartition_iff _ _).mpr hT2) hne01 hne02 hne12

/-- The second gadget: for an offset `R + δ` just above a power `R`, an explicit source at `R + δ −
1` and the three-pair merge at two different starting deficits give three good partitions. -/
theorem three_le_count_sub_above {Q R δ t s : ℕ} (hR : R = 3 ^ s) (hs : 4 ≤ s)
    (hδ : δ = 1 ∨ δ = 2 ∨ δ = 3 ∨ δ = 4 ∨ δ = 6) (hQ : Q = 3 ^ t) (hQR : 3 * R ≤ Q) :
    3 ≤ count (Q - (R + δ)) := by
  have hδ1 : 1 ≤ δ ∧ δ ≤ 6 := by omega
  have hR81 : 81 ≤ R := by
    rw [hR]
    calc (81 : ℕ) = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hRz : (R : ℤ) = (3 : ℤ) ^ s := by exact_mod_cast hR
  have hQz : (Q : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hQ
  have hRodd : R % 2 = 1 := by rw [hR]; exact pow_three_odd_sub s
  obtain ⟨a, haR⟩ : ∃ a : ℤ, (R : ℤ) = 2 * a + 1 := ⟨((R : ℤ) - 1) / 2, by omega⟩
  have ha40 : 40 ≤ a := by omega
  obtain ⟨e, he2, he6, hδe⟩ : ∃ e : ℤ, 2 ≤ e ∧ e ≤ 6 ∧ (δ : ℤ) ≤ e :=
    ⟨max (δ : ℤ) 2, by omega, by omega, by omega⟩
  obtain ⟨src, hsrc, hpair⟩ := srcAbove_exists hR hs hδ
  obtain ⟨T₀, hT0def⟩ : ∃ X, X = targetC (Q : ℤ) ((R + δ : ℕ) : ℤ) src := ⟨_, rfl⟩
  have hT0 : GoodOn (interval (Q - (R + δ))) T₀ := by
    rw [hT0def]
    exact targetC_goodOn hQ (by omega) (by omega) hsrc
  have hmemsrc : ∀ X ∈ src, X ∈ T₀ := by
    intro X hX
    rw [hT0def]
    simp only [targetC]
    exact Finset.mem_union.mpr (Or.inl hX)
  have hmemcan : ∀ d : ℤ, ((R + δ : ℕ) : ℤ) ≤ d → 2 * d < (Q : ℤ) →
      ({d, (Q : ℤ) - d} : Finset ℤ) ∈ T₀ := by
    intro d h1 h2
    rw [hT0def]
    simp only [targetC, canonicalPairs]
    refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨d, ?_, rfl⟩))
    simp only [Finset.mem_Icc]
    omega
  have hdmem : ({(R : ℤ) + e, (Q : ℤ) - ((R : ℤ) + e)} : Finset ℤ) ∈ T₀ :=
    hmemcan ((R : ℤ) + e) (by omega) (by omega)
  have key : ∀ c : ℤ, 4 ≤ c → c ≤ 5 → ∃ T : Finset (Finset ℤ),
      GoodOn (interval (Q - (R + δ))) T ∧
        ({(R : ℤ) - a, (R : ℤ) - (a - e + 1), (Q : ℤ) - ((R : ℤ) + e)} : Finset ℤ) ∈ T ∧
        ({(R : ℤ) + e, c, (Q : ℤ) - ((R : ℤ) + e + c)} : Finset ℤ) ∈ T ∧
        ∀ d : ℤ, ((R + δ : ℕ) : ℤ) ≤ d → 2 * d < (Q : ℤ) → d ≠ (R : ℤ) + e →
          d ≠ (R : ℤ) + e + c → d ≠ (R : ℤ) + (a - e + 1) - c →
          ({d, (Q : ℤ) - d} : Finset ℤ) ∈ T := by
    intro c hc4 hc5
    refine ⟨(T₀ \ {{a, (R : ℤ) - a}, {a - e + 1, (R : ℤ) - (a - e + 1)}, {c, (R : ℤ) - c},
      {(R : ℤ) + e, (Q : ℤ) - ((R : ℤ) + e)},
      {(R : ℤ) + e + c, (Q : ℤ) - ((R : ℤ) + e + c)},
      {(R : ℤ) + (a - e + 1) - c, (Q : ℤ) - ((R : ℤ) + (a - e + 1) - c)}}) ∪
      {{(R : ℤ) - a, (R : ℤ) - (a - e + 1), (Q : ℤ) - ((R : ℤ) + e)},
        {(R : ℤ) + e, c, (Q : ℤ) - ((R : ℤ) + e + c)},
        {(R : ℤ) - c, a - e + 1, (Q : ℤ) - ((R : ℤ) + (a - e + 1) - c)},
        {a, (R : ℤ) + e + c, (R : ℤ) + (a - e + 1) - c}}, ?_, ?_, ?_, ?_⟩
    · refine goodOn_replace hT0 ?_ ?_
      · intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hmemsrc _ (hpair a (by omega) (by omega) (by omega))
        · exact hmemsrc _ (hpair (a - e + 1) (by omega) (by omega) (by omega))
        · exact hmemsrc _ (hpair c (by omega) (by omega) (by omega))
        · exact hmemcan _ (by omega) (by omega)
        · exact hmemcan _ (by omega) (by omega)
        · exact hmemcan _ (by omega) (by omega)
      · have hCgood : GoodOn
            (({{(R : ℤ) - a, (R : ℤ) - (a - e + 1), (Q : ℤ) - ((R : ℤ) + e)},
              {(R : ℤ) + e, c, (Q : ℤ) - ((R : ℤ) + e + c)},
              {(R : ℤ) - c, a - e + 1, (Q : ℤ) - ((R : ℤ) + (a - e + 1) - c)},
              {a, (R : ℤ) + e + c, (R : ℤ) + (a - e + 1) - c}} :
                Finset (Finset ℤ)).biUnion id)
            ({{(R : ℤ) - a, (R : ℤ) - (a - e + 1), (Q : ℤ) - ((R : ℤ) + e)},
              {(R : ℤ) + e, c, (Q : ℤ) - ((R : ℤ) + e + c)},
              {(R : ℤ) - c, a - e + 1, (Q : ℤ) - ((R : ℤ) + (a - e + 1) - c)},
              {a, (R : ℤ) + e + c, (R : ℤ) + (a - e + 1) - c}} : Finset (Finset ℤ)) := by
          apply goodOn_of_blocks
          · intro X hX
            simp only [Finset.mem_insert, Finset.mem_singleton] at hX
            rcases hX with rfl | rfl | rfl | rfl
            · exact goodBlock_triple (by omega) (by omega) (by omega) (k := t)
                (by rw [← hQz]; omega)
            · exact goodBlock_triple (by omega) (by omega) (by omega) (k := t)
                (by rw [← hQz]; omega)
            · exact goodBlock_triple (by omega) (by omega) (by omega) (k := t)
                (by rw [← hQz]; omega)
            · refine goodBlock_triple (by omega) (by omega) (by omega) (k := s + 1) ?_
              rw [pow_succ, ← hRz]
              omega
          · intro X hX Y hY hXY
            simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
            apply Finset.disjoint_left.mpr
            intro x hx hy
            rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;>
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;>
              first
                | exact absurd rfl hXY
                | omega
        have hsupp : ({{(R : ℤ) - a, (R : ℤ) - (a - e + 1), (Q : ℤ) - ((R : ℤ) + e)},
              {(R : ℤ) + e, c, (Q : ℤ) - ((R : ℤ) + e + c)},
              {(R : ℤ) - c, a - e + 1, (Q : ℤ) - ((R : ℤ) + (a - e + 1) - c)},
              {a, (R : ℤ) + e + c, (R : ℤ) + (a - e + 1) - c}} :
                Finset (Finset ℤ)).biUnion id =
            ({{a, (R : ℤ) - a}, {a - e + 1, (R : ℤ) - (a - e + 1)}, {c, (R : ℤ) - c},
              {(R : ℤ) + e, (Q : ℤ) - ((R : ℤ) + e)},
              {(R : ℤ) + e + c, (Q : ℤ) - ((R : ℤ) + e + c)},
              {(R : ℤ) + (a - e + 1) - c, (Q : ℤ) - ((R : ℤ) + (a - e + 1) - c)}} :
                Finset (Finset ℤ)).biUnion id := by
          simp only [Finset.biUnion_insert, Finset.singleton_biUnion, id_eq]
          ext x
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          omega
        rw [hsupp] at hCgood
        exact hCgood
    · exact Finset.mem_union.mpr (Or.inr (by simp))
    · exact Finset.mem_union.mpr (Or.inr (by simp))
    · intro d hd1 hd2 hd3 hd4 hd5
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hmemcan d hd1 hd2, ?_⟩))
      intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hd : d ∈ ({d, (Q : ℤ) - d} : Finset ℤ) := by simp
      rcases hmem with h | h | h | h | h | h <;> rw [h] at hd <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd <;> omega
  obtain ⟨T₁, hT1, hT1a, hT1b, hT1c⟩ := key 4 (by norm_num) (by norm_num)
  obtain ⟨T₂, hT2, hT2a, hT2b, hT2c⟩ := key 5 (by norm_num) (by norm_num)
  have hne01 : T₀ ≠ T₁ := by
    refine ne_of_block_mem hT1 hdmem hT1a ((Q : ℤ) - ((R : ℤ) + e)) (by simp) (by simp) ?_
    intro h
    have hmem : (R : ℤ) + e ∈
        ({(R : ℤ) - a, (R : ℤ) - (a - e + 1), (Q : ℤ) - ((R : ℤ) + e)} : Finset ℤ) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hne02 : T₀ ≠ T₂ := by
    refine ne_of_block_mem hT2 hdmem hT2a ((Q : ℤ) - ((R : ℤ) + e)) (by simp) (by simp) ?_
    intro h
    have hmem : (R : ℤ) + e ∈
        ({(R : ℤ) - a, (R : ℤ) - (a - e + 1), (Q : ℤ) - ((R : ℤ) + e)} : Finset ℤ) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hne12 : T₁ ≠ T₂ := by
    have hmem2 : ({(R : ℤ) + e + 4, (Q : ℤ) - ((R : ℤ) + e + 4)} : Finset ℤ) ∈ T₂ :=
      hT2c ((R : ℤ) + e + 4) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ne_of_block_mem hT2 hT1b hmem2 ((Q : ℤ) - ((R : ℤ) + e + 4)) (by simp) (by simp) ?_
    intro h
    have hmem : (4 : ℤ) ∈ ({(R : ℤ) + e + 4, (Q : ℤ) - ((R : ℤ) + e + 4)} : Finset ℤ) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  exact three_le_count ((isGoodPartition_iff _ _).mpr hT0) ((isGoodPartition_iff _ _).mpr hT1)
    ((isGoodPartition_iff _ _).mpr hT2) hne01 hne02 hne12

end

end GNM

import GNM.Forced

/-!
# The lift between two powers and its inverse

Along one family of offsets the good partitions of `{1, …, Q − r}` and of `{1, …, Q' − r}`
correspond to each other: relabel every element above the halfway point of `Q` by the gap `Q' − Q`
and insert the canonical pairs `{d, Q' − d}` for the deficits in between. The inverse operation
drops those pairs and relabels back, and it is inverse precisely because above the threshold every
large deficit is forced to be canonical, so the pairs to drop are present in every good partition of
the larger interval. The same pair of maps works at the positive offsets, with the threshold `r(r +
1)`.
-/

namespace GNM

open GN

noncomputable section

/-- The canonical pairs `{d, Q − d}` for the deficits `d` in a range. -/
def canonicalPairs (Q lo hi : ℤ) : Finset (Finset ℤ) :=
  (Finset.Icc lo hi).image (fun d => {d, Q - d})

/-- The canonical pairs of a range partition the range and its complement. -/
theorem canonicalPairs_goodOn {Q t : ℕ} {lo hi : ℤ} (hQ : Q = 3 ^ t) (hlo : 1 ≤ lo)
    (hhi : 2 * hi < (Q : ℤ)) :
    GoodOn (Finset.Icc lo hi ∪ Finset.Icc ((Q : ℤ) - hi) ((Q : ℤ) - lo))
      (canonicalPairs (Q : ℤ) lo hi) := by
  have hQ' : (Q : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hQ
  have hgood : ∀ d ∈ Finset.Icc lo hi, GoodBlock ({d, (Q : ℤ) - d} : Finset ℤ) := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    exact goodBlock_pair (by omega) (k := t) (by rw [← hQ']; ring)
  have hdisj : ∀ d ∈ Finset.Icc lo hi, ∀ e ∈ Finset.Icc lo hi, d ≠ e →
      Disjoint ({d, (Q : ℤ) - d} : Finset ℤ) ({e, (Q : ℤ) - e} : Finset ℤ) := by
    intro d hd e he hde
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    obtain ⟨he1, he2⟩ := Finset.mem_Icc.mp he
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    omega
  have himg := goodOn_image (Finset.Icc lo hi) (fun d => ({d, (Q : ℤ) - d} : Finset ℤ)) hgood hdisj
  have hset : (Finset.Icc lo hi).biUnion (fun d => ({d, (Q : ℤ) - d} : Finset ℤ)) =
      Finset.Icc lo hi ∪ Finset.Icc ((Q : ℤ) - hi) ((Q : ℤ) - lo) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
      Finset.mem_Icc]
    constructor
    · rintro ⟨d, hd, hx | hx⟩ <;> omega
    · intro hx
      rcases hx with hx | hx
      · exact ⟨x, by omega, Or.inl rfl⟩
      · exact ⟨(Q : ℤ) - x, by omega, Or.inr (by omega)⟩
  rw [hset] at himg
  exact himg

/-- The lift from `Q` to `Q'`: relabel every element above the halfway point of `Q` by the gap, and
add the canonical pairs for the deficits in between. -/
def liftBlocks (Q Q' : ℤ) (bs : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  bs.image (fun b => b.image (fun x => if (Q - 1) / 2 < x then x + (Q' - Q) else x)) ∪
    canonicalPairs Q' ((Q + 1) / 2) ((Q' - 1) / 2)

/-! ### The relabelling and its reverse -/

/-- Every power of three is odd. -/
private theorem pow_three_odd' (t : ℕ) : 3 ^ t % 2 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-- The relabelling that moves everything above the halfway point of `Q` up by the gap. -/
private def relabel (Q Q' x : ℤ) : ℤ := if (Q - 1) / 2 < x then x + (Q' - Q) else x

/-- The reverse relabelling, which moves everything above the halfway point of `Q'` down by the
gap. -/
private def unrelabel (Q Q' x : ℤ) : ℤ := if (Q' - 1) / 2 < x then x - (Q' - Q) else x

/-- The lift, with the relabelling named. -/
private theorem liftBlocks_eq (Q Q' : ℤ) (bs : Finset (Finset ℤ)) :
    liftBlocks Q Q' bs = bs.image (fun b => b.image (relabel Q Q')) ∪
      canonicalPairs Q' ((Q + 1) / 2) ((Q' - 1) / 2) := rfl

/-- Below the halfway point the relabelling does nothing. -/
private theorem relabel_of_le {Q Q' x : ℤ} (h : x ≤ (Q - 1) / 2) : relabel Q Q' x = x := by
  simp only [relabel]
  rw [if_neg (by omega)]

/-- Above the halfway point the relabelling adds the gap. -/
private theorem relabel_of_gt {Q Q' x : ℤ} (h : (Q - 1) / 2 < x) :
    relabel Q Q' x = x + (Q' - Q) := by
  simp only [relabel]
  rw [if_pos h]

/-- Below the halfway point of `Q'` the reverse relabelling does nothing. -/
private theorem unrelabel_of_le {Q Q' x : ℤ} (h : x ≤ (Q' - 1) / 2) : unrelabel Q Q' x = x := by
  simp only [unrelabel]
  rw [if_neg (by omega)]

/-- Above the halfway point of `Q'` the reverse relabelling subtracts the gap. -/
private theorem unrelabel_of_gt {Q Q' x : ℤ} (h : (Q' - 1) / 2 < x) :
    unrelabel Q Q' x = x - (Q' - Q) := by
  simp only [unrelabel]
  rw [if_pos h]

/-- The relabelling is injective. -/
private theorem relabel_injective {Q Q' : ℤ} (hle : Q ≤ Q') :
    Function.Injective (relabel Q Q') := by
  intro x y hxy
  simp only [relabel] at hxy
  split at hxy <;> split at hxy <;> omega

/-- The reverse relabelling undoes the relabelling. -/
private theorem unrelabel_relabel {Q Q' : ℤ} (hle : Q ≤ Q') (x : ℤ) :
    unrelabel Q Q' (relabel Q Q' x) = x := by
  by_cases h : (Q - 1) / 2 < x
  · rw [relabel_of_gt h, unrelabel_of_gt (by omega)]
    ring
  · rw [relabel_of_le (by omega), unrelabel_of_le (by omega)]

/-- Relabelling a block adds the gap once for every element above the halfway point. -/
private theorem relabel_sum {Q Q' : ℤ} (hle : Q ≤ Q') (b : Finset ℤ) :
    (b.image (relabel Q Q')).sum id
      = b.sum id + (Q' - Q) * ((b.filter (fun y => (Q - 1) / 2 < y)).card : ℤ) := by
  rw [Finset.sum_image (fun x _ y _ h => relabel_injective hle h)]
  have hcongr : ∀ x ∈ b, id (relabel Q Q' x)
      = id x + (if (Q - 1) / 2 < x then Q' - Q else 0) := by
    intro x hx
    by_cases h : (Q - 1) / 2 < x
    · rw [relabel_of_gt h, if_pos h]
      simp
    · rw [relabel_of_le (by omega), if_neg h]
      simp
  rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, ← Finset.sum_filter]
  simp [Finset.sum_const, mul_comm]
  ring

/-- The relabelled blocks of a good partition are a good partition of the relabelled set, once the
relabelled block sums are known to be powers of three. -/
private theorem relabel_goodOn {Q Q' : ℤ} {s : Finset ℤ} {bs : Finset (Finset ℤ)}
    (hle : Q ≤ Q') (hbs : GoodOn s bs)
    (hsums : ∀ b ∈ bs, ∃ k : ℕ, (b.image (relabel Q Q')).sum id = (3 : ℤ) ^ k) :
    GoodOn (s.image (relabel Q Q')) (bs.image (fun b => b.image (relabel Q Q'))) := by
  have hinj := relabel_injective hle
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.image_biUnion, ← hbs.1, Finset.biUnion_image]
    simp only [id_eq]
  · intro u hu v hv huv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    have hbc : b ≠ c := fun h => huv (by rw [h])
    have hd := hbs.2.1 b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x', hx', hxx⟩ := Finset.mem_image.mp hy'
    have hxe : x' = x := hinj hxx
    subst hxe
    exact Finset.disjoint_left.mp hd hx hx'
  · intro u hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
    have hgood := hbs.block hb
    exact ⟨hgood.1.image _, le_trans Finset.card_image_le hgood.2.1, hsums b hb⟩

/-! ### The lift carries good partitions to good partitions -/

/-- The lift carries good partitions at a negative offset to good partitions at the same offset of
the larger power. -/
theorem liftBlocks_goodOn_sub {Q Q' r t t' : ℕ} (hQ : Q = 3 ^ t) (hQ' : Q' = 3 ^ t')
    (hle : Q ≤ Q') (hr : 1 ≤ r) (hQr : 2 * r < Q) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (Q - r)) bs) :
    GoodOn (interval (Q' - r)) (liftBlocks (Q : ℤ) (Q' : ℤ) bs) := by
  have hQo : Q % 2 = 1 := by rw [hQ]; exact pow_three_odd' t
  have hQ'o : Q' % 2 = 1 := by rw [hQ']; exact pow_three_odd' t'
  have hleZ : (Q : ℤ) ≤ (Q' : ℤ) := by exact_mod_cast hle
  obtain ⟨c, hc⟩ : ∃ c : ℤ, 2 * c = (Q : ℤ) - 1 := ⟨((Q : ℤ) - 1) / 2, by omega⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℤ, 2 * c' = (Q' : ℤ) - 1 := ⟨((Q' : ℤ) - 1) / 2, by omega⟩
  have hcc : ((Q : ℤ) - 1) / 2 = c := by omega
  have hcc' : ((Q' : ℤ) - 1) / 2 = c' := by omega
  have hsums : ∀ b ∈ bs, ∃ k : ℕ, (b.image (relabel (Q : ℤ) (Q' : ℤ))).sum id = (3 : ℤ) ^ k := by
    intro b hb
    have hbmem : ∀ y ∈ b, 1 ≤ y ∧ y ≤ (Q : ℤ) - (r : ℤ) := by
      intro y hy
      have h := hbs.subset hb hy
      simp only [interval, Finset.mem_Icc] at h
      omega
    by_cases hhigh : ∃ x ∈ b, c < x
    · obtain ⟨x, hx, hxc⟩ := hhigh
      obtain ⟨hsum, hlow⟩ := high_block_sub hQ hQr hbs hb hx (by omega)
      have hfilter : b.filter (fun y => ((Q : ℤ) - 1) / 2 < y) = {x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hy, hyc⟩
          by_contra hne
          have := hlow y hy hne
          omega
        · rintro rfl
          exact ⟨hx, by omega⟩
      have hQ'Z : (Q' : ℤ) = (3 : ℤ) ^ t' := by exact_mod_cast hQ'
      refine ⟨t', ?_⟩
      rw [relabel_sum hleZ, hfilter, hsum]
      simp only [Finset.card_singleton, Nat.cast_one, mul_one]
      omega
    · push_neg at hhigh
      obtain ⟨k, hk⟩ := (hbs.block hb).2.2
      refine ⟨k, ?_⟩
      have hfilter : b.filter (fun y => ((Q : ℤ) - 1) / 2 < y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro y hy
        have := hhigh y hy
        omega
      rw [relabel_sum hleZ, hfilter, hk]
      simp
  have hgood := relabel_goodOn hleZ hbs hsums
  have hcan := canonicalPairs_goodOn (Q := Q') (t := t') (lo := ((Q : ℤ) + 1) / 2)
    (hi := ((Q' : ℤ) - 1) / 2) hQ' (by omega) (by omega)
  have hsupp : (interval (Q - r)).image (relabel (Q : ℤ) (Q' : ℤ))
      = Finset.Icc 1 c ∪ Finset.Icc ((Q' : ℤ) - c) ((Q' : ℤ) - (r : ℤ)) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_Icc, interval, relabel]
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      split <;> omega
    · intro hy
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨y, ⟨by omega, by omega⟩, by rw [if_neg (by omega)]⟩
      · exact ⟨y - ((Q' : ℤ) - (Q : ℤ)), ⟨by omega, by omega⟩, by
          rw [if_pos (by omega)]; ring⟩
  have hdisj : Disjoint ((interval (Q - r)).image (relabel (Q : ℤ) (Q' : ℤ)))
      (Finset.Icc (((Q : ℤ) + 1) / 2) (((Q' : ℤ) - 1) / 2) ∪
        Finset.Icc ((Q' : ℤ) - ((Q' : ℤ) - 1) / 2) ((Q' : ℤ) - ((Q : ℤ) + 1) / 2)) := by
    rw [hsupp, Finset.disjoint_left]
    intro y hy hy'
    simp only [Finset.mem_union, Finset.mem_Icc] at hy hy'
    omega
  have hsupp2 : (interval (Q - r)).image (relabel (Q : ℤ) (Q' : ℤ)) ∪
      (Finset.Icc (((Q : ℤ) + 1) / 2) (((Q' : ℤ) - 1) / 2) ∪
        Finset.Icc ((Q' : ℤ) - ((Q' : ℤ) - 1) / 2) ((Q' : ℤ) - ((Q : ℤ) + 1) / 2))
      = interval (Q' - r) := by
    rw [hsupp]
    ext y
    simp only [Finset.mem_union, Finset.mem_Icc, interval]
    omega
  have hu := GoodOn.union hgood hcan hdisj
  rw [hsupp2] at hu
  rw [liftBlocks_eq]
  exact hu

/-- The lift carries good partitions at a positive offset to good partitions at the same offset of
the larger power. -/
theorem liftBlocks_goodOn_add {P P' r t t' : ℕ} (hP : P = 3 ^ t) (hP' : P' = 3 ^ t')
    (hle : P ≤ P') (hPr : r * (r + 1) < P) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (P + r)) bs) :
    GoodOn (interval (P' + r)) (liftBlocks (P : ℤ) (P' : ℤ) bs) := by
  have hPo : P % 2 = 1 := by rw [hP]; exact pow_three_odd' t
  have hP'o : P' % 2 = 1 := by rw [hP']; exact pow_three_odd' t'
  have hleZ : (P : ℤ) ≤ (P' : ℤ) := by exact_mod_cast hle
  have hPrZ : (r : ℤ) * ((r : ℤ) + 1) < (P : ℤ) := by exact_mod_cast hPr
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
  have hrP : (r : ℤ) < (P : ℤ) := by nlinarith
  obtain ⟨c, hc⟩ : ∃ c : ℤ, 2 * c = (P : ℤ) - 1 := ⟨((P : ℤ) - 1) / 2, by omega⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℤ, 2 * c' = (P' : ℤ) - 1 := ⟨((P' : ℤ) - 1) / 2, by omega⟩
  have hcc : ((P : ℤ) - 1) / 2 = c := by omega
  have hcc' : ((P' : ℤ) - 1) / 2 = c' := by omega
  have hPZ : (P : ℤ) = (3 : ℤ) ^ t := by exact_mod_cast hP
  have hP'Z : (P' : ℤ) = (3 : ℤ) ^ t' := by exact_mod_cast hP'
  have hsums : ∀ b ∈ bs, ∃ k : ℕ, (b.image (relabel (P : ℤ) (P' : ℤ))).sum id = (3 : ℤ) ^ k := by
    intro b hb
    have hbmem : ∀ y ∈ b, 1 ≤ y ∧ y ≤ (P : ℤ) + (r : ℤ) := by
      intro y hy
      have h := hbs.subset hb hy
      simp only [interval, Finset.mem_Icc] at h
      omega
    by_cases hhigh : ∃ x ∈ b, c < x
    · obtain ⟨x, hx, hxc⟩ := hhigh
      rcases high_block_add hP hPr hbs hb hx (by omega) with hsing | ⟨hsum, hlow⟩ | ⟨hsum, hhi⟩
      · have hfilter : b.filter (fun y => ((P : ℤ) - 1) / 2 < y) = {(P : ℤ)} := by
          rw [hsing, Finset.filter_singleton, if_pos (by omega)]
        refine ⟨t', ?_⟩
        rw [relabel_sum hleZ, hfilter, hsing]
        simp only [Finset.card_singleton, Nat.cast_one, mul_one, Finset.sum_singleton, id_eq]
        omega
      · have hfilter : b.filter (fun y => ((P : ℤ) - 1) / 2 < y) = {x} := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hy, hyc⟩
            by_contra hne
            have := hlow y hy hne
            omega
          · rintro rfl
            exact ⟨hx, by omega⟩
        refine ⟨t', ?_⟩
        rw [relabel_sum hleZ, hfilter, hsum]
        simp only [Finset.card_singleton, Nat.cast_one, mul_one]
        omega
      · have hfilter : b.filter (fun y => ((P : ℤ) - 1) / 2 < y) = b := by
          rw [Finset.filter_eq_self]
          intro y hy
          have := hhi y hy
          omega
        have hcard3 : b.card = 3 := by
          by_contra hne
          have hc2 : b.card ≤ 2 := by
            have := (hbs.block hb).2.1
            omega
          have h := Finset.sum_le_card_nsmul b id ((P : ℤ) + (r : ℤ))
            (fun y hy => (hbmem y hy).2)
          have hle2 : b.sum id ≤ (b.card : ℤ) * ((P : ℤ) + (r : ℤ)) := by
            simpa [nsmul_eq_mul] using h
          have hcard2 : (b.card : ℤ) ≤ 2 := by exact_mod_cast hc2
          have hPle : (P : ℤ) ≤ 2 * (r : ℤ) := by nlinarith
          nlinarith [sq_nonneg (2 * (r : ℤ) - 1)]
        refine ⟨t' + 1, ?_⟩
        rw [relabel_sum hleZ, hfilter, hsum, hcard3]
        have h3 : (3 : ℤ) ^ (t' + 1) = 3 * (3 : ℤ) ^ t' := by ring
        rw [h3, ← hP'Z]
        push_cast
        ring
    · push_neg at hhigh
      obtain ⟨k, hk⟩ := (hbs.block hb).2.2
      refine ⟨k, ?_⟩
      have hfilter : b.filter (fun y => ((P : ℤ) - 1) / 2 < y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro y hy
        have := hhigh y hy
        omega
      rw [relabel_sum hleZ, hfilter, hk]
      simp
  have hgood := relabel_goodOn hleZ hbs hsums
  have hcan := canonicalPairs_goodOn (Q := P') (t := t') (lo := ((P : ℤ) + 1) / 2)
    (hi := ((P' : ℤ) - 1) / 2) hP' (by omega) (by omega)
  have hsupp : (interval (P + r)).image (relabel (P : ℤ) (P' : ℤ))
      = Finset.Icc 1 c ∪ Finset.Icc ((P' : ℤ) - c) ((P' : ℤ) + (r : ℤ)) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_Icc, interval, relabel]
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      push_cast at hx2
      split <;> omega
    · intro hy
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨y, ⟨by omega, ?_⟩, by rw [if_neg (by omega)]⟩
        push_cast
        omega
      · refine ⟨y - ((P' : ℤ) - (P : ℤ)), ⟨by omega, ?_⟩, by rw [if_pos (by omega)]; ring⟩
        push_cast
        omega
  have hdisj : Disjoint ((interval (P + r)).image (relabel (P : ℤ) (P' : ℤ)))
      (Finset.Icc (((P : ℤ) + 1) / 2) (((P' : ℤ) - 1) / 2) ∪
        Finset.Icc ((P' : ℤ) - ((P' : ℤ) - 1) / 2) ((P' : ℤ) - ((P : ℤ) + 1) / 2)) := by
    rw [hsupp, Finset.disjoint_left]
    intro y hy hy'
    simp only [Finset.mem_union, Finset.mem_Icc] at hy hy'
    omega
  have hsupp2 : (interval (P + r)).image (relabel (P : ℤ) (P' : ℤ)) ∪
      (Finset.Icc (((P : ℤ) + 1) / 2) (((P' : ℤ) - 1) / 2) ∪
        Finset.Icc ((P' : ℤ) - ((P' : ℤ) - 1) / 2) ((P' : ℤ) - ((P : ℤ) + 1) / 2))
      = interval (P' + r) := by
    rw [hsupp]
    ext y
    simp only [Finset.mem_union, Finset.mem_Icc, interval]
    push_cast
    omega
  have hu := GoodOn.union hgood hcan hdisj
  rw [hsupp2] at hu
  rw [liftBlocks_eq]
  exact hu

/-- The truncation: drop the canonical pairs for the deficits between the two halfway points and
relabel back. -/
def truncBlocks (Q Q' : ℤ) (bs : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  (bs \ canonicalPairs Q' ((Q + 1) / 2) ((Q' - 1) / 2)).image
    (fun b => b.image (fun x => if (Q' - 1) / 2 < x then x - (Q' - Q) else x))

/-- The truncation undoes the lift at a negative offset. -/
theorem truncBlocks_liftBlocks_sub {Q Q' r t t' : ℕ} (hQ : Q = 3 ^ t) (hQ' : Q' = 3 ^ t')
    (hle : Q ≤ Q') (hr : 1 ≤ r) (hQr : 2 * r < Q) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (Q - r)) bs) :
    truncBlocks (Q : ℤ) (Q' : ℤ) (liftBlocks (Q : ℤ) (Q' : ℤ) bs) = bs := by
  sorry

/-- The truncation undoes the lift at a positive offset. -/
theorem truncBlocks_liftBlocks_add {P P' r t t' : ℕ} (hP : P = 3 ^ t) (hP' : P' = 3 ^ t')
    (hle : P ≤ P') (hPr : r * (r + 1) < P) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (P + r)) bs) :
    truncBlocks (P : ℤ) (P' : ℤ) (liftBlocks (P : ℤ) (P' : ℤ) bs) = bs := by
  sorry

/-- Above the threshold the lift undoes the truncation at a negative offset, and the truncation of a
good partition is a good partition of the smaller interval. -/
theorem liftBlocks_truncBlocks_sub {Q Q' r t t' : ℕ} (hQ : Q = 3 ^ t) (hQ' : Q' = 3 ^ t')
    (hle : Q ≤ Q') (hr : 1 ≤ r) (hQr : 2 * r < Q) (hthr : r * (r - 1) < Q)
    {bs : Finset (Finset ℤ)} (hbs : GoodOn (interval (Q' - r)) bs) :
    liftBlocks (Q : ℤ) (Q' : ℤ) (truncBlocks (Q : ℤ) (Q' : ℤ) bs) = bs ∧
      GoodOn (interval (Q - r)) (truncBlocks (Q : ℤ) (Q' : ℤ) bs) := by
  sorry

/-- Above the threshold the lift undoes the truncation at a positive offset, and the truncation of a
good partition is a good partition of the smaller interval. -/
theorem liftBlocks_truncBlocks_add {P P' r t t' : ℕ} (hP : P = 3 ^ t) (hP' : P' = 3 ^ t')
    (hle : P ≤ P') (hthr : r * (r + 1) < P) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (P' + r)) bs) :
    liftBlocks (P : ℤ) (P' : ℤ) (truncBlocks (P : ℤ) (P' : ℤ) bs) = bs ∧
      GoodOn (interval (P + r)) (truncBlocks (P : ℤ) (P' : ℤ) bs) := by
  sorry

/-- The counts at a negative offset are monotone along the powers. -/
theorem count_sub_le_count_sub {r t t' : ℕ} (hr : 1 ≤ r) (h2 : 2 * r < 3 ^ t) (htt' : t ≤ t') :
    count (3 ^ t - r) ≤ count (3 ^ t' - r) := by
  sorry

end

end GNM

import GNM.Basic

/-!
# Forced blocks and forced deficits

Above the halfway point of a power of three the shape of a block is forced: a block containing a
large element sums to the power (or, just above the power, either to the power with one large
element or to three times the power with three large elements), and its remaining elements are
small. Counting the mass of the small elements against the deficits they have to supply then forces
every large deficit to be canonical, that is, to be one of the pairs `{d, Q − d}`. These are the two
facts the truncation of the lift rests on, and with them the counts are constant along each family
of powers.
-/

namespace GNM

open GN

noncomputable section

/-! ### Arithmetic and counting helpers -/

/-- Every power of three is odd. -/
private theorem pow_three_odd (t : ℕ) : 3 ^ t % 2 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-- Twice the sum of the integers from one to `m` is `m(m + 1)`. -/
private theorem two_mul_sum_Icc (m : ℕ) :
    2 * ∑ x ∈ Finset.Icc (1 : ℤ) (m : ℤ), x = (m : ℤ) * ((m : ℤ) + 1) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, Finset.Icc_eq_empty (by omega)]
    simp
  | succ n ih =>
    have hins : Finset.Icc (1 : ℤ) ((n : ℤ) + 1)
        = insert ((n : ℤ) + 1) (Finset.Icc (1 : ℤ) (n : ℤ)) := by
      ext y
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : ((n : ℤ) + 1) ∉ Finset.Icc (1 : ℤ) (n : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    push_cast
    rw [hins, Finset.sum_insert hnot]
    linear_combination ih

/-- The block of a partition that contains a given element. -/
private def blockOf (bs : Finset (Finset ℤ)) (x : ℤ) : Finset ℤ :=
  if h : ∃ b ∈ bs, x ∈ b then h.choose else ∅

/-- An element covered by a partition lies in the block the partition assigns to it. -/
private theorem blockOf_spec {bs : Finset (Finset ℤ)} {x : ℤ} (h : ∃ b ∈ bs, x ∈ b) :
    blockOf bs x ∈ bs ∧ x ∈ blockOf bs x := by
  have hb : blockOf bs x = h.choose := dif_pos h
  rw [hb]
  exact h.choose_spec

/-- The blocks of a partition are disjoint, so the block assigned to an element is the only block
containing it. -/
private theorem blockOf_eq {s : Finset ℤ} {bs : Finset (Finset ℤ)} (hbs : GoodOn s bs)
    {b : Finset ℤ} (hb : b ∈ bs) {x : ℤ} (hx : x ∈ b) : blockOf bs x = b := by
  obtain ⟨hmem, hxmem⟩ := blockOf_spec (⟨b, hb, hx⟩ : ∃ b ∈ bs, x ∈ b)
  by_contra hne
  exact Finset.disjoint_left.mp (hbs.2.1 _ hmem b hb hne) hxmem hx

/-- The sum of a two-element block. -/
private theorem sum_pair_id {x y : ℤ} (h : x ≠ y) : ({x, y} : Finset ℤ).sum id = x + y :=
  Finset.sum_pair h

/-- An element of a block of nonnegative integers is at most the sum of the block. -/
private theorem le_block_sum {b : Finset ℤ} (hpos : ∀ y ∈ b, (0 : ℤ) ≤ y) {x : ℤ} (hx : x ∈ b) :
    x ≤ b.sum id :=
  Finset.single_le_sum (f := id) (fun i hi => hpos i hi) hx

/-- Two distinct elements of a block of nonnegative integers sum to at most the sum of the
block. -/
private theorem pair_le_block_sum {b : Finset ℤ} (hpos : ∀ y ∈ b, (0 : ℤ) ≤ y) {x y : ℤ}
    (hx : x ∈ b) (hy : y ∈ b) (hxy : x ≠ y) : x + y ≤ b.sum id := by
  have hsub : ({x, y} : Finset ℤ) ⊆ b := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  rw [← sum_pair_id hxy]
  exact Finset.sum_le_sum_of_subset_of_nonneg (f := id) hsub (fun i hi _ => hpos i hi)

/-- A block of at most three elements, one of them `x` and all the others at most `C`, has sum at
most `x + 2C`. -/
private theorem block_sum_le {b : Finset ℤ} (hcard : b.card ≤ 3) {x : ℤ} (hx : x ∈ b) {C : ℤ}
    (hC : ∀ y ∈ b, y ≠ x → y ≤ C) (hC0 : 0 ≤ C) : b.sum id ≤ x + 2 * C := by
  have herase : x + (b.erase x).sum id = b.sum id := Finset.add_sum_erase b id hx
  have hb : (b.erase x).sum id ≤ ((b.erase x).card : ℤ) * C := by
    have h := Finset.sum_le_card_nsmul (b.erase x) id C
      (fun y hy => hC y (Finset.mem_of_mem_erase hy) (Finset.mem_erase.mp hy).1)
    simpa [nsmul_eq_mul] using h
  have hcard2 : ((b.erase x).card : ℤ) ≤ 2 := by
    have hce := Finset.card_erase_of_mem hx
    have h3 : (b.erase x).card ≤ 2 := by omega
    exact_mod_cast h3
  nlinarith

/-- At most two distinct integers, each at most `M`, sum to at most `2M − 1`. -/
private theorem sum_le_of_card_le_two {s : Finset ℤ} (hcard : s.card ≤ 2) {M : ℤ} (hM : 1 ≤ M)
    (hub : ∀ z ∈ s, z ≤ M) : s.sum id ≤ 2 * M - 1 := by
  rcases eq_or_lt_of_le hcard with hc | hc
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc
    have hu := hub u (by simp)
    have hv := hub v (by simp)
    rw [sum_pair_id huv]
    omega
  · have h1 : s.card ≤ 1 := by omega
    have h := Finset.sum_le_card_nsmul s id M (fun z hz => hub z hz)
    have hc1 : (s.card : ℤ) ≤ 1 := by exact_mod_cast h1
    have hle : s.sum id ≤ (s.card : ℤ) * M := by simpa [nsmul_eq_mul] using h
    nlinarith

/-- A set of positive integers whose sum is one of its own elements is that single element. -/
private theorem eq_singleton_of_sum {s : Finset ℤ} (hpos : ∀ y ∈ s, (1 : ℤ) ≤ y) {a : ℤ}
    (ha : a ∈ s) (hsum : s.sum id = a) : s = {a} := by
  have herase : a + (s.erase a).sum id = s.sum id := Finset.add_sum_erase s id ha
  have hempty : s.erase a = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h1 : (1 : ℤ) ≤ y := hpos y (Finset.mem_of_mem_erase hy)
    have h2 : y ≤ (s.erase a).sum id :=
      le_block_sum (fun z hz => by
        have := hpos z (Finset.mem_of_mem_erase hz)
        omega) hy
    omega
  have hins := Finset.insert_erase ha
  rw [hempty] at hins
  simpa using hins.symm

/-! ### The forced form of a block meeting the upper half -/

/-- Negative offsets: a block containing an element above the halfway point sums to the power, and
its other elements lie below the halfway point. -/
theorem high_block_sub {Q r t : ℕ} (hQ : Q = 3 ^ t) (hQr : 2 * r < Q) {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval (Q - r)) bs) {b : Finset ℤ} (hb : b ∈ bs) {x : ℤ} (hx : x ∈ b)
    (hhigh : ((Q : ℤ) - 1) / 2 < x) :
    b.sum id = Q ∧ ∀ y ∈ b, y ≠ x → y ≤ ((Q : ℤ) - 1) / 2 := by
  have hQ' : (Q : ℤ) = 3 ^ t := by exact_mod_cast hQ
  have hodd : Q % 2 = 1 := by rw [hQ]; exact pow_three_odd t
  have hgood := hbs.block hb
  obtain ⟨k, hk⟩ := hgood.2.2
  have hmem : ∀ y ∈ b, 1 ≤ y ∧ y ≤ (Q : ℤ) - (r : ℤ) := by
    intro y hy
    have h := hbs.subset hb hy
    simp only [interval, Finset.mem_Icc] at h
    omega
  have hpos : ∀ y ∈ b, (0 : ℤ) ≤ y := by
    intro y hy
    have := (hmem y hy).1
    omega
  have hxb := hmem x hx
  have hlow : x ≤ b.sum id := le_block_sum hpos hx
  have hupper : b.sum id < 3 * (Q : ℤ) := by
    by_cases hxM : x = (Q : ℤ) - (r : ℤ)
    · have h := block_sum_le hgood.2.1 hx (C := (Q : ℤ) - (r : ℤ) - 1)
        (fun y hy hyx => by
          have := hmem y hy
          omega) (by omega)
      omega
    · have h := block_sum_le hgood.2.1 hx (C := (Q : ℤ) - (r : ℤ))
        (fun y hy _ => (hmem y hy).2) (by omega)
      omega
  have hsum : b.sum id = (Q : ℤ) := power_three_between hQ' hk (by omega) hupper
  refine ⟨hsum, ?_⟩
  intro y hy hyx
  by_contra hcon
  push_neg at hcon
  have hpair := pair_le_block_sum hpos hx hy (Ne.symm hyx)
  omega

/-- Positive offsets above the threshold `r(r + 1)`: a block meeting the upper half is the singleton
of the power, or sums to the power with exactly one high element, or sums to three times the power
with all three elements high. -/
theorem high_block_add {P r t : ℕ} (hP : P = 3 ^ t) (hPr : r * (r + 1) < P)
    {bs : Finset (Finset ℤ)} (hbs : GoodOn (interval (P + r)) bs) {b : Finset ℤ} (hb : b ∈ bs)
    {x : ℤ} (hx : x ∈ b) (hhigh : ((P : ℤ) - 1) / 2 < x) :
    b = {(P : ℤ)} ∨ (b.sum id = P ∧ ∀ y ∈ b, y ≠ x → y ≤ ((P : ℤ) - 1) / 2) ∨
      (b.sum id = 3 * P ∧ ∀ y ∈ b, ((P : ℤ) - 1) / 2 < y) := by
  have hP' : (P : ℤ) = 3 ^ t := by exact_mod_cast hP
  have hodd : P % 2 = 1 := by rw [hP]; exact pow_three_odd t
  have hPrZ : (r : ℤ) * ((r : ℤ) + 1) < (P : ℤ) := by exact_mod_cast hPr
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
  have hrP : (r : ℤ) < (P : ℤ) := by nlinarith
  have hcdiv : 2 * (((P : ℤ) - 1) / 2) = (P : ℤ) - 1 := by omega
  have hgood := hbs.block hb
  obtain ⟨k, hk⟩ := hgood.2.2
  have hmem : ∀ y ∈ b, 1 ≤ y ∧ y ≤ (P : ℤ) + (r : ℤ) := by
    intro y hy
    have h := hbs.subset hb hy
    simp only [interval, Finset.mem_Icc] at h
    omega
  have hpos : ∀ y ∈ b, (0 : ℤ) ≤ y := by
    intro y hy
    have := (hmem y hy).1
    omega
  have hxb := hmem x hx
  have hlow : x ≤ b.sum id := le_block_sum hpos hx
  have hupper : b.sum id < 9 * (P : ℤ) := by
    have h := block_sum_le hgood.2.1 hx (C := (P : ℤ) + (r : ℤ))
      (fun y hy _ => (hmem y hy).2) (by omega)
    omega
  have hsumcases : b.sum id = (P : ℤ) ∨ b.sum id = 3 * (P : ℤ) := by
    by_cases hlt : b.sum id < 3 * (P : ℤ)
    · exact Or.inl (power_three_between hP' hk (by omega) hlt)
    · have h3P : (3 : ℤ) * (P : ℤ) = 3 ^ (t + 1) := by rw [hP']; ring
      exact Or.inr (power_three_between h3P hk (by omega) (by omega))
  rcases hsumcases with hsum | hsum
  · refine Or.inr (Or.inl ⟨hsum, ?_⟩)
    intro y hy hyx
    by_contra hcon
    push_neg at hcon
    have hpair := pair_le_block_sum hpos hx hy (Ne.symm hyx)
    omega
  · refine Or.inr (Or.inr ⟨hsum, ?_⟩)
    intro y hy
    by_contra hcon
    push_neg at hcon
    have hb2 : (b.erase y).card ≤ 2 := by
      have hce := Finset.card_erase_of_mem hy
      have := hgood.2.1
      omega
    have hs2 : (b.erase y).sum id ≤ 2 * ((P : ℤ) + (r : ℤ)) - 1 :=
      sum_le_of_card_le_two hb2 (by omega)
        (fun z hz => (hmem z (Finset.mem_of_mem_erase hz)).2)
    have herase : y + (b.erase y).sum id = b.sum id := Finset.add_sum_erase b id hy
    have hkey : (P : ℤ) ≤ 4 * (r : ℤ) - 3 := by omega
    nlinarith [hPrZ, hkey, sq_nonneg (2 * (r : ℤ) - 3)]

/-! ### The conserved mass of the blocks below the halfway point -/

/-- The blocks that lie entirely below the halfway point carry a bounded mass: if every block that
meets the upper half is accounted for by its high elements, twice the sum of such a block is at most
the total mass of the interval less the mass of the blocks meeting the upper half. -/
private theorem low_only_le {N : ℕ} {c P : ℤ} {bs : Finset (Finset ℤ)}
    (hbs : GoodOn (interval N) bs) (hc0 : 0 ≤ c) (hcN : c ≤ (N : ℤ))
    (hhb : ∀ b ∈ bs, ∀ x ∈ b, c < x →
      b.sum id = P * ((b.filter (fun y => c < y)).card : ℤ))
    {C : Finset ℤ} (hC : C ∈ bs) (hClow : ∀ y ∈ C, y ≤ c) :
    2 * C.sum id ≤ (N : ℤ) * ((N : ℤ) + 1) - 2 * P * ((N : ℤ) - c) := by
  have hpos : ∀ b ∈ bs, ∀ y ∈ b, (1 : ℤ) ≤ y := by
    intro b hb y hy
    have h := hbs.subset hb hy
    simp only [interval, Finset.mem_Icc] at h
    exact h.1
  have hsumpos : ∀ b ∈ bs, (0 : ℤ) ≤ b.sum id := by
    intro b hb
    apply Finset.sum_nonneg
    intro y hy
    have := hpos b hb y hy
    simp only [id_eq]
    omega
  have hCfilter : C ∈ bs.filter (fun b => ∀ y ∈ b, y ≤ c) := Finset.mem_filter.mpr ⟨hC, hClow⟩
  have hCle : C.sum id ≤ ∑ b ∈ bs.filter (fun b => ∀ y ∈ b, y ≤ c), b.sum id :=
    Finset.single_le_sum (f := fun b => b.sum id)
      (fun b hb => hsumpos b (Finset.mem_filter.mp hb).1) hCfilter
  have hdisj : (bs : Set (Finset ℤ)).PairwiseDisjoint id := fun u hu v hv huv =>
    hbs.2.1 u hu v hv huv
  have htot : ∑ b ∈ bs, b.sum id = ∑ x ∈ Finset.Icc (1 : ℤ) (N : ℤ), x := by
    have h := Finset.sum_biUnion (s := bs) (t := (id : Finset ℤ → Finset ℤ))
      (f := fun x : ℤ => x) hdisj
    rw [hbs.1] at h
    simp only [interval, id_eq] at h ⊢
    exact h.symm
  have hAsum : ∑ b ∈ bs.filter (fun b => ¬ ∀ y ∈ b, y ≤ c), b.sum id
      = P * ∑ b ∈ bs.filter (fun b => ¬ ∀ y ∈ b, y ≤ c),
          ((b.filter (fun y => c < y)).card : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    push_neg at hb2
    obtain ⟨y, hy, hy2⟩ := hb2
    exact hhb b hb1 y hy hy2
  have hhighcount : ∑ b ∈ bs, ((b.filter (fun y => c < y)).card : ℤ) = (N : ℤ) - c := by
    have hbu : bs.biUnion (fun b => b.filter (fun y => c < y)) = Finset.Icc (c + 1) (N : ℤ) := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨b, hb, hzb, hzc⟩
        have h := hbs.subset hb hzb
        simp only [interval, Finset.mem_Icc] at h
        omega
      · intro hz
        have hzi : z ∈ interval N := by
          simp only [interval, Finset.mem_Icc]
          omega
        rw [← hbs.1] at hzi
        obtain ⟨b, hb, hzb⟩ := Finset.mem_biUnion.mp hzi
        exact ⟨b, hb, hzb, by omega⟩
    have hcb : (bs.biUnion (fun b => b.filter (fun y => c < y))).card
        = ∑ b ∈ bs, (b.filter (fun y => c < y)).card := by
      apply Finset.card_biUnion
      intro u hu v hv huv
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        (hbs.2.1 u hu v hv huv)
    rw [hbu] at hcb
    have hIcc : ((Finset.Icc (c + 1) (N : ℤ)).card : ℤ) = (N : ℤ) - c := by
      rw [Int.card_Icc_of_le (c + 1) (N : ℤ) (by omega)]
      ring
    have hcast : ((∑ b ∈ bs, (b.filter (fun y => c < y)).card : ℕ) : ℤ) = (N : ℤ) - c := by
      rw [← hcb, hIcc]
    push_cast at hcast
    exact hcast
  have hzero : ∑ b ∈ bs.filter (fun b => ∀ y ∈ b, y ≤ c),
      ((b.filter (fun y => c < y)).card : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    have hempty : b.filter (fun y => c < y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y hy
      have := hb2 y hy
      omega
    rw [hempty]
    simp
  have hsplit1 := Finset.sum_filter_add_sum_filter_not bs (fun b => ∀ y ∈ b, y ≤ c)
    (fun b => b.sum id)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not bs (fun b => ∀ y ∈ b, y ≤ c)
    (fun b => ((b.filter (fun y => c < y)).card : ℤ))
  have hgauss := two_mul_sum_Icc N
  have hA2 : ∑ b ∈ bs.filter (fun b => ¬ ∀ y ∈ b, y ≤ c),
      ((b.filter (fun y => c < y)).card : ℤ) = (N : ℤ) - c := by
    linarith [hzero, hsplit2, hhighcount]
  rw [hA2] at hAsum
  linarith [hCle, htot, hAsum, hsplit1, hgauss]

/-- The largest non-canonical deficit would have to lie inside a still larger one: if every deficit
above the low mass has a low part summing to it, and every low number above the low mass lies in the
low part of a deficit at least as large, then every such deficit is canonical. -/
private theorem descent {c S : ℤ} (_hS : 0 ≤ S) (Lo : ℤ → Finset ℤ)
    (hsum : ∀ e : ℤ, S < e → e ≤ c → (Lo e).sum id = e)
    (hpos : ∀ e : ℤ, S < e → e ≤ c → ∀ y ∈ Lo e, (1 : ℤ) ≤ y)
    (hstep : ∀ x : ℤ, S < x → x ≤ c → ∃ e : ℤ, x ≤ e ∧ e ≤ c ∧ x ∈ Lo e) :
    ∀ e : ℤ, S < e → e ≤ c → Lo e = {e} := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨e₁, he₁S, he₁c, he₁ne⟩ := hcon
  have hTne : ((Finset.Icc (S + 1) c).filter (fun e => Lo e ≠ {e})).Nonempty :=
    ⟨e₁, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, he₁c⟩, he₁ne⟩⟩
  obtain ⟨e₀, he₀eq⟩ :
      ∃ e, e = ((Finset.Icc (S + 1) c).filter (fun e => Lo e ≠ {e})).max' hTne := ⟨_, rfl⟩
  have hmax : ∀ z ∈ (Finset.Icc (S + 1) c).filter (fun e => Lo e ≠ {e}), z ≤ e₀ := by
    intro z hz
    rw [he₀eq]
    exact Finset.le_max' _ z hz
  have he₀mem := Finset.max'_mem _ hTne
  rw [← he₀eq] at he₀mem
  obtain ⟨he₀I, he₀ne⟩ := Finset.mem_filter.mp he₀mem
  obtain ⟨he₀1, he₀c⟩ := Finset.mem_Icc.mp he₀I
  have he₀S : S < e₀ := by omega
  have hsum₀ := hsum e₀ he₀S he₀c
  have hpos₀ := hpos e₀ he₀S he₀c
  have hlt : ∀ y ∈ Lo e₀, y < e₀ := by
    intro y hy
    rcases lt_or_ge y e₀ with h | h
    · exact h
    · exfalso
      have hle : y ≤ (Lo e₀).sum id :=
        le_block_sum (fun z hz => by
          have := hpos₀ z hz
          omega) hy
      have hy0 : y = e₀ := by omega
      rw [hy0] at hy
      exact he₀ne (eq_singleton_of_sum hpos₀ hy hsum₀)
  obtain ⟨e', hge, hle', hmem'⟩ := hstep e₀ he₀S he₀c
  have hne' : e' ≠ e₀ := by
    intro h
    rw [h] at hmem'
    exact absurd (hlt e₀ hmem') (by omega)
  have he'T : e' ∈ (Finset.Icc (S + 1) c).filter (fun e => Lo e ≠ {e}) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle'⟩, ?_⟩
    intro hcon'
    rw [hcon'] at hmem'
    simp only [Finset.mem_singleton] at hmem'
    exact hne' hmem'.symm
  have hfin := hmax e' he'T
  omega

/-! ### Every large deficit is canonical -/

/-- Negative offsets: every deficit above `r(r − 1)/2` is canonical. -/
theorem canonical_sub {Q r t : ℕ} (hQ : Q = 3 ^ t) (hr : 1 ≤ r) (hQr : 2 * r < Q)
    {bs : Finset (Finset ℤ)} (hbs : GoodOn (interval (Q - r)) bs) {d : ℤ}
    (hd : (r : ℤ) * (r - 1) / 2 < d) (hdr : (r : ℤ) ≤ d) (hd' : 2 * d < Q) :
    ({d, (Q : ℤ) - d} : Finset ℤ) ∈ bs := by
  have hodd : Q % 2 = 1 := by rw [hQ]; exact pow_three_odd t
  have hr1 : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  obtain ⟨c, hc2⟩ : ∃ c : ℤ, 2 * c = (Q : ℤ) - 1 := ⟨((Q : ℤ) - 1) / 2, by omega⟩
  have hcc : ((Q : ℤ) - 1) / 2 = c := by omega
  have hNc : ((Q - r : ℕ) : ℤ) = (Q : ℤ) - (r : ℤ) := by omega
  obtain ⟨S, hS2⟩ : ∃ S : ℤ, 2 * S = (r : ℤ) * ((r : ℤ) - 1) := by
    rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨(k : ℤ) * ((r : ℤ) - 1), by subst hk; push_cast; ring⟩
    · exact ⟨(r : ℤ) * (k : ℤ), by subst hk; push_cast; ring⟩
  have hSd : S < d := by omega
  have hS0 : 0 ≤ S := by nlinarith
  have hSr : (r : ℤ) - 1 ≤ S := by
    rcases lt_or_ge (r : ℤ) 2 with h | h
    · have hval : (r : ℤ) = 1 := by omega
      rw [hval] at hS2
      omega
    · nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (r : ℤ) - 1)
        (by linarith : (0 : ℤ) ≤ (r : ℤ) - 2)]
  -- the forced form of the block of a high element
  have hhighblk : ∀ z : ℤ, c < z → z ≤ (Q : ℤ) - (r : ℤ) →
      blockOf bs z ∈ bs ∧ z ∈ blockOf bs z ∧ (blockOf bs z).sum id = (Q : ℤ) ∧
        ∀ y ∈ blockOf bs z, y ≠ z → y ≤ c := by
    intro z hz1 hz2
    have hzmem : z ∈ interval (Q - r) := by
      simp only [interval, Finset.mem_Icc]
      omega
    have hex : ∃ b ∈ bs, z ∈ b := by
      rw [← hbs.1] at hzmem
      simpa using Finset.mem_biUnion.mp hzmem
    obtain ⟨hb1, hb2⟩ := blockOf_spec hex
    obtain ⟨hsum, hlow⟩ := high_block_sub hQ hQr hbs hb1 hb2 (by omega)
    refine ⟨hb1, hb2, hsum, fun y hy hyz => ?_⟩
    have := hlow y hy hyz
    omega
  -- every block meeting the upper half is accounted for by its single high element
  have hhb : ∀ b ∈ bs, ∀ x ∈ b, c < x →
      b.sum id = (Q : ℤ) * ((b.filter (fun y => c < y)).card : ℤ) := by
    intro b hb x hx hxc
    have hxle : x ≤ (Q : ℤ) - (r : ℤ) := by
      have h := hbs.subset hb hx
      simp only [interval, Finset.mem_Icc] at h
      omega
    obtain ⟨hsum, hlow⟩ := high_block_sub hQ hQr hbs hb hx (by omega)
    have hfilter : b.filter (fun y => c < y) = {x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, hyc⟩
        by_contra hne
        have := hlow y hy hne
        omega
      · rintro rfl
        exact ⟨hx, hxc⟩
    rw [hfilter, hsum]
    simp
  -- the blocks below the halfway point are small
  have hlowmass : ∀ C ∈ bs, (∀ y ∈ C, y ≤ c) → C.sum id ≤ S := by
    intro C hC hClow
    have h := low_only_le hbs (by omega) (by omega) hhb hC hClow
    have hkey : ((Q - r : ℕ) : ℤ) * (((Q - r : ℕ) : ℤ) + 1)
        - 2 * (Q : ℤ) * (((Q - r : ℕ) : ℤ) - c) = 2 * S := by
      rw [hNc, hS2]
      have hQc : (Q : ℤ) = 2 * c + 1 := by omega
      rw [hQc]
      ring
    linarith
  -- the low part of the block of a high element
  have hLoblock : ∀ e : ℤ, S < e → e ≤ c →
      blockOf bs ((Q : ℤ) - e) ∈ bs ∧
      blockOf bs ((Q : ℤ) - e)
          = insert ((Q : ℤ) - e) ((blockOf bs ((Q : ℤ) - e)).filter (fun y => y ≤ c)) ∧
      ((blockOf bs ((Q : ℤ) - e)).filter (fun y => y ≤ c)).sum id = e ∧
      ∀ y ∈ (blockOf bs ((Q : ℤ) - e)).filter (fun y => y ≤ c), (1 : ℤ) ≤ y := by
    intro e heS hec
    obtain ⟨hb1, hb2, hsum, hlow⟩ := hhighblk ((Q : ℤ) - e) (by omega) (by omega)
    have hins : blockOf bs ((Q : ℤ) - e)
        = insert ((Q : ℤ) - e) ((blockOf bs ((Q : ℤ) - e)).filter (fun y => y ≤ c)) := by
      ext y
      simp only [Finset.mem_insert, Finset.mem_filter]
      constructor
      · intro hy
        by_cases hyz : y = (Q : ℤ) - e
        · exact Or.inl hyz
        · exact Or.inr ⟨hy, hlow y hy hyz⟩
      · rintro (rfl | ⟨hy, -⟩)
        · exact hb2
        · exact hy
    have hnotmem : ((Q : ℤ) - e) ∉ (blockOf bs ((Q : ℤ) - e)).filter (fun y => y ≤ c) := by
      simp only [Finset.mem_filter, not_and]
      intro _
      omega
    have hsplit : (blockOf bs ((Q : ℤ) - e)).sum id
        = ((Q : ℤ) - e) + ((blockOf bs ((Q : ℤ) - e)).filter (fun y => y ≤ c)).sum id := by
      conv_lhs => rw [hins]
      rw [Finset.sum_insert hnotmem]
      simp
    refine ⟨hb1, hins, by omega, ?_⟩
    intro y hy
    have hyb := (Finset.mem_filter.mp hy).1
    have h := hbs.subset hb1 hyb
    simp only [interval, Finset.mem_Icc] at h
    exact h.1
  -- a low number above the mass lies in the low part of a deficit at least as large
  have hstep : ∀ x : ℤ, S < x → x ≤ c →
      ∃ e : ℤ, x ≤ e ∧ e ≤ c ∧ x ∈ (blockOf bs ((Q : ℤ) - e)).filter (fun y => y ≤ c) := by
    intro x hxS hxc
    have hxmem : x ∈ interval (Q - r) := by
      simp only [interval, Finset.mem_Icc]
      omega
    have hex : ∃ b ∈ bs, x ∈ b := by
      rw [← hbs.1] at hxmem
      simpa using Finset.mem_biUnion.mp hxmem
    obtain ⟨hC1, hC2⟩ := blockOf_spec hex
    by_cases hlowonly : ∀ y ∈ blockOf bs x, y ≤ c
    · exfalso
      have h1 := hlowmass _ hC1 hlowonly
      have h2 : x ≤ (blockOf bs x).sum id := by
        refine le_block_sum (fun y hy => ?_) hC2
        have h := hbs.subset hC1 hy
        simp only [interval, Finset.mem_Icc] at h
        omega
      omega
    · push_neg at hlowonly
      obtain ⟨z, hz, hzc⟩ := hlowonly
      have hzle : z ≤ (Q : ℤ) - (r : ℤ) := by
        have h := hbs.subset hC1 hz
        simp only [interval, Finset.mem_Icc] at h
        omega
      obtain ⟨hb1, hb2, hsumz, hlowz⟩ := hhighblk z (by omega) hzle
      have hxz : blockOf bs z = blockOf bs x := blockOf_eq hbs hC1 hz
      have hxin : x ∈ blockOf bs z := by rw [hxz]; exact hC2
      have hpair : x + z ≤ (blockOf bs z).sum id := by
        refine pair_le_block_sum (fun y hy => ?_) hxin hb2 (by omega)
        have h := hbs.subset hb1 hy
        simp only [interval, Finset.mem_Icc] at h
        omega
      refine ⟨(Q : ℤ) - z, by omega, by omega, ?_⟩
      have hQz : (Q : ℤ) - ((Q : ℤ) - z) = z := by ring
      rw [hQz]
      exact Finset.mem_filter.mpr ⟨hxin, hxc⟩
  have hdc : d ≤ c := by omega
  have hdescent := descent hS0 (fun e => (blockOf bs ((Q : ℤ) - e)).filter (fun y => y ≤ c))
    (fun e h1 h2 => (hLoblock e h1 h2).2.2.1) (fun e h1 h2 => (hLoblock e h1 h2).2.2.2) hstep
  have hfin := hdescent d hSd hdc
  obtain ⟨hb1, hins, -, -⟩ := hLoblock d hSd hdc
  rw [hfin] at hins
  have hpair : ({d, (Q : ℤ) - d} : Finset ℤ) = blockOf bs ((Q : ℤ) - d) := by
    rw [hins]
    exact Finset.pair_comm d ((Q : ℤ) - d)
  rw [hpair]
  exact hb1

/-- Positive offsets: every deficit above `r(r + 1)/2` is canonical. -/
theorem canonical_add {P r t : ℕ} (hP : P = 3 ^ t) (hPr : r * (r + 1) < P)
    {bs : Finset (Finset ℤ)} (hbs : GoodOn (interval (P + r)) bs) {d : ℤ}
    (hd : (r : ℤ) * (r + 1) / 2 < d) (hd1 : 1 ≤ d) (hd' : 2 * d < P) :
    ({d, (P : ℤ) - d} : Finset ℤ) ∈ bs := by
  have hodd : P % 2 = 1 := by rw [hP]; exact pow_three_odd t
  have hPrZ : (r : ℤ) * ((r : ℤ) + 1) < (P : ℤ) := by exact_mod_cast hPr
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
  have hrP : (r : ℤ) < (P : ℤ) := by nlinarith
  obtain ⟨c, hc2⟩ : ∃ c : ℤ, 2 * c = (P : ℤ) - 1 := ⟨((P : ℤ) - 1) / 2, by omega⟩
  have hcc : ((P : ℤ) - 1) / 2 = c := by omega
  have hNc : ((P + r : ℕ) : ℤ) = (P : ℤ) + (r : ℤ) := by push_cast; ring
  obtain ⟨S, hS2⟩ : ∃ S : ℤ, 2 * S = (r : ℤ) * ((r : ℤ) + 1) := by
    rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨(k : ℤ) * ((r : ℤ) + 1), by subst hk; push_cast; ring⟩
    · exact ⟨(r : ℤ) * ((k : ℤ) + 1), by subst hk; push_cast; ring⟩
  have hSd : S < d := by omega
  have hS0 : 0 ≤ S := by nlinarith
  have hrr : (0 : ℤ) ≤ ((r : ℤ) - 1) * ((r : ℤ) - 2) := by
    rcases lt_or_ge (r : ℤ) 2 with h | h
    · nlinarith
    · exact mul_nonneg (by linarith) (by linarith)
  have hS2r : 2 * (r : ℤ) - 1 ≤ S := by nlinarith
  -- the forced form of the block of a high element
  have hhighblk : ∀ z : ℤ, c < z → z ≤ (P : ℤ) + (r : ℤ) →
      blockOf bs z ∈ bs ∧ z ∈ blockOf bs z ∧
        (((blockOf bs z).sum id = (P : ℤ) ∧ ∀ y ∈ blockOf bs z, y ≠ z → y ≤ c) ∨
          ((blockOf bs z).sum id = 3 * (P : ℤ) ∧ ∀ y ∈ blockOf bs z, c < y)) := by
    intro z hz1 hz2
    have hzmem : z ∈ interval (P + r) := by
      simp only [interval, Finset.mem_Icc]
      omega
    have hex : ∃ b ∈ bs, z ∈ b := by
      rw [← hbs.1] at hzmem
      simpa using Finset.mem_biUnion.mp hzmem
    obtain ⟨hb1, hb2⟩ := blockOf_spec hex
    refine ⟨hb1, hb2, ?_⟩
    rcases high_block_add hP hPr hbs hb1 hb2 (by omega) with hsing | ⟨hsum, hlow⟩ | ⟨hsum, hhi⟩
    · left
      refine ⟨by rw [hsing]; simp, fun y hy hyz => ?_⟩
      rw [hsing] at hy
      rw [hsing] at hb2
      simp only [Finset.mem_singleton] at hy hb2
      exact absurd (hy.trans hb2.symm) hyz
    · left
      exact ⟨hsum, fun y hy hyz => by
        have := hlow y hy hyz
        omega⟩
    · right
      exact ⟨hsum, fun y hy => by
        have := hhi y hy
        omega⟩
  -- every block meeting the upper half is accounted for by its high elements
  have hhb : ∀ b ∈ bs, ∀ x ∈ b, c < x →
      b.sum id = (P : ℤ) * ((b.filter (fun y => c < y)).card : ℤ) := by
    intro b hb x hx hxc
    have hgood := hbs.block hb
    have hmem : ∀ y ∈ b, 1 ≤ y ∧ y ≤ (P : ℤ) + (r : ℤ) := by
      intro y hy
      have h := hbs.subset hb hy
      simp only [interval, Finset.mem_Icc] at h
      omega
    have hxle := hmem x hx
    rcases high_block_add hP hPr hbs hb hx (by omega) with hsing | ⟨hsum, hlow⟩ | ⟨hsum, hhi⟩
    · have hxP : x = (P : ℤ) := by
        rw [hsing] at hx
        simpa using hx
      have hfilter : b.filter (fun y => c < y) = {(P : ℤ)} := by
        rw [hsing, Finset.filter_singleton, if_pos (by omega)]
      rw [hfilter, hsing]
      simp
    · have hfilter : b.filter (fun y => c < y) = {x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hy, hyc⟩
          by_contra hne
          have := hlow y hy hne
          omega
        · rintro rfl
          exact ⟨hx, hxc⟩
      rw [hfilter, hsum]
      simp
    · have hfilter : b.filter (fun y => c < y) = b := by
        rw [Finset.filter_eq_self]
        intro y hy
        have := hhi y hy
        omega
      have hcard3 : b.card = 3 := by
        by_contra hne
        have hc2' : b.card ≤ 2 := by
          have := hgood.2.1
          omega
        have h := Finset.sum_le_card_nsmul b id ((P : ℤ) + (r : ℤ))
          (fun y hy => (hmem y hy).2)
        have hle : b.sum id ≤ (b.card : ℤ) * ((P : ℤ) + (r : ℤ)) := by
          simpa [nsmul_eq_mul] using h
        have hcard2 : (b.card : ℤ) ≤ 2 := by exact_mod_cast hc2'
        have hPle : (P : ℤ) ≤ 2 * (r : ℤ) := by nlinarith
        nlinarith [sq_nonneg (2 * (r : ℤ) - 1)]
      rw [hfilter, hsum, hcard3]
      push_cast
      ring
  -- the blocks below the halfway point are small
  have hlowmass : ∀ C ∈ bs, (∀ y ∈ C, y ≤ c) → C.sum id ≤ S := by
    intro C hC hClow
    have h := low_only_le hbs (by omega) (by omega) hhb hC hClow
    have hkey : ((P + r : ℕ) : ℤ) * (((P + r : ℕ) : ℤ) + 1)
        - 2 * (P : ℤ) * (((P + r : ℕ) : ℤ) - c) = 2 * S := by
      rw [hNc, hS2]
      have hPc : (P : ℤ) = 2 * c + 1 := by omega
      rw [hPc]
      ring
    linarith
  -- the low part of the block of a high element
  have hLoblock : ∀ e : ℤ, S < e → e ≤ c →
      blockOf bs ((P : ℤ) - e) ∈ bs ∧
      blockOf bs ((P : ℤ) - e)
          = insert ((P : ℤ) - e) ((blockOf bs ((P : ℤ) - e)).filter (fun y => y ≤ c)) ∧
      ((blockOf bs ((P : ℤ) - e)).filter (fun y => y ≤ c)).sum id = e ∧
      ∀ y ∈ (blockOf bs ((P : ℤ) - e)).filter (fun y => y ≤ c), (1 : ℤ) ≤ y := by
    intro e heS hec
    obtain ⟨hb1, hb2, hcases⟩ := hhighblk ((P : ℤ) - e) (by omega) (by omega)
    have hsingle : (blockOf bs ((P : ℤ) - e)).sum id = (P : ℤ) ∧
        ∀ y ∈ blockOf bs ((P : ℤ) - e), y ≠ (P : ℤ) - e → y ≤ c := by
      rcases hcases with h | ⟨hsum, hhi⟩
      · exact h
      · exfalso
        have hmem : ∀ y ∈ blockOf bs ((P : ℤ) - e), 1 ≤ y ∧ y ≤ (P : ℤ) + (r : ℤ) := by
          intro y hy
          have h := hbs.subset hb1 hy
          simp only [interval, Finset.mem_Icc] at h
          omega
        have hcard := (hbs.block hb1).2.1
        have hb2' : ((blockOf bs ((P : ℤ) - e)).erase ((P : ℤ) - e)).card ≤ 2 := by
          have hce := Finset.card_erase_of_mem hb2
          omega
        have hs2 : ((blockOf bs ((P : ℤ) - e)).erase ((P : ℤ) - e)).sum id
            ≤ 2 * ((P : ℤ) + (r : ℤ)) - 1 :=
          sum_le_of_card_le_two hb2' (by omega)
            (fun z hz => (hmem z (Finset.mem_of_mem_erase hz)).2)
        have herase : ((P : ℤ) - e)
            + ((blockOf bs ((P : ℤ) - e)).erase ((P : ℤ) - e)).sum id
            = (blockOf bs ((P : ℤ) - e)).sum id :=
          Finset.add_sum_erase _ id hb2
        omega
    obtain ⟨hsum, hlow⟩ := hsingle
    have hins : blockOf bs ((P : ℤ) - e)
        = insert ((P : ℤ) - e) ((blockOf bs ((P : ℤ) - e)).filter (fun y => y ≤ c)) := by
      ext y
      simp only [Finset.mem_insert, Finset.mem_filter]
      constructor
      · intro hy
        by_cases hyz : y = (P : ℤ) - e
        · exact Or.inl hyz
        · exact Or.inr ⟨hy, hlow y hy hyz⟩
      · rintro (rfl | ⟨hy, -⟩)
        · exact hb2
        · exact hy
    have hnotmem : ((P : ℤ) - e) ∉ (blockOf bs ((P : ℤ) - e)).filter (fun y => y ≤ c) := by
      simp only [Finset.mem_filter, not_and]
      intro _
      omega
    have hsplit : (blockOf bs ((P : ℤ) - e)).sum id
        = ((P : ℤ) - e) + ((blockOf bs ((P : ℤ) - e)).filter (fun y => y ≤ c)).sum id := by
      conv_lhs => rw [hins]
      rw [Finset.sum_insert hnotmem]
      simp
    refine ⟨hb1, hins, by omega, ?_⟩
    intro y hy
    have hyb := (Finset.mem_filter.mp hy).1
    have h := hbs.subset hb1 hyb
    simp only [interval, Finset.mem_Icc] at h
    exact h.1
  -- a low number above the mass lies in the low part of a deficit at least as large
  have hstep : ∀ x : ℤ, S < x → x ≤ c →
      ∃ e : ℤ, x ≤ e ∧ e ≤ c ∧ x ∈ (blockOf bs ((P : ℤ) - e)).filter (fun y => y ≤ c) := by
    intro x hxS hxc
    have hxmem : x ∈ interval (P + r) := by
      simp only [interval, Finset.mem_Icc]
      omega
    have hex : ∃ b ∈ bs, x ∈ b := by
      rw [← hbs.1] at hxmem
      simpa using Finset.mem_biUnion.mp hxmem
    obtain ⟨hC1, hC2⟩ := blockOf_spec hex
    by_cases hlowonly : ∀ y ∈ blockOf bs x, y ≤ c
    · exfalso
      have h1 := hlowmass _ hC1 hlowonly
      have h2 : x ≤ (blockOf bs x).sum id := by
        refine le_block_sum (fun y hy => ?_) hC2
        have h := hbs.subset hC1 hy
        simp only [interval, Finset.mem_Icc] at h
        omega
      omega
    · push_neg at hlowonly
      obtain ⟨z, hz, hzc⟩ := hlowonly
      have hzle : z ≤ (P : ℤ) + (r : ℤ) := by
        have h := hbs.subset hC1 hz
        simp only [interval, Finset.mem_Icc] at h
        omega
      obtain ⟨hb1, hb2, hcases⟩ := hhighblk z (by omega) hzle
      have hxz : blockOf bs z = blockOf bs x := blockOf_eq hbs hC1 hz
      have hxin : x ∈ blockOf bs z := by rw [hxz]; exact hC2
      have hsum : (blockOf bs z).sum id = (P : ℤ) := by
        rcases hcases with ⟨hsum, -⟩ | ⟨-, hhi⟩
        · exact hsum
        · exact absurd (hhi x hxin) (by omega)
      have hpair : x + z ≤ (blockOf bs z).sum id := by
        refine pair_le_block_sum (fun y hy => ?_) hxin hb2 (by omega)
        have h := hbs.subset hb1 hy
        simp only [interval, Finset.mem_Icc] at h
        omega
      refine ⟨(P : ℤ) - z, by omega, by omega, ?_⟩
      have hPz : (P : ℤ) - ((P : ℤ) - z) = z := by ring
      rw [hPz]
      exact Finset.mem_filter.mpr ⟨hxin, hxc⟩
  have hdc : d ≤ c := by omega
  have hdescent := descent hS0 (fun e => (blockOf bs ((P : ℤ) - e)).filter (fun y => y ≤ c))
    (fun e h1 h2 => (hLoblock e h1 h2).2.2.1) (fun e h1 h2 => (hLoblock e h1 h2).2.2.2) hstep
  have hfin := hdescent d hSd hdc
  obtain ⟨hb1, hins, -, -⟩ := hLoblock d hSd hdc
  rw [hfin] at hins
  have hpair : ({d, (P : ℤ) - d} : Finset ℤ) = blockOf bs ((P : ℤ) - d) := by
    rw [hins]
    exact Finset.pair_comm d ((P : ℤ) - d)
  rw [hpair]
  exact hb1

end

end GNM

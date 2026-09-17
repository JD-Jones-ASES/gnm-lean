import GN.Elementary
import GN.Signed
import GN.Contraction

namespace GN
noncomputable section

/-- Complete the missing complementary pairs below a power of three. -/
theorem complete_complement_orbits {P n : ℤ} {t : ℕ} {s : Finset ℤ}
    (hP : P = (3 : ℤ)^t) (hn : P ≤ n)
    (hs : HasGood s) (hsub : s ⊆ Finset.Icc 1 n)
    (htop : Finset.Icc P n ⊆ s)
    (hsymm : ∀ x : ℤ, 1 ≤ x → x < P → (x ∈ s ↔ P-x ∈ s)) :
    HasGood (Finset.Icc 1 n) := by
  have hPpos : 0 < P := by rw [hP]; positivity
  have hodd : Odd P := by rw [hP]; exact (by decide : Odd (3 : ℤ)).pow
  obtain ⟨h, hh⟩ := hodd
  have hp : P = 2*h+1 := by omega
  let u := (Finset.Icc 1 h).filter (fun x => x ∉ s)
  let f : ℤ → Finset ℤ := fun x => {x, P-x}
  have hpair := hasGood_biUnion u f
    (by
      intro x hx
      have hx' : 1 ≤ x ∧ x ≤ h ∧ x ∉ s := by
        simpa only [u, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hx
      apply goodBlock_pair (by omega) (k := t)
      omega)
    (by
      intro x hx y hy hxy
      have hx' : 1 ≤ x ∧ x ≤ h ∧ x ∉ s := by
        simpa only [u, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hx
      have hy' : 1 ≤ y ∧ y ≤ h ∧ y ∉ s := by
        simpa only [u, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hy
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      simp only [f, Finset.mem_insert, Finset.mem_singleton] at hz hz'
      omega)
  have hd : Disjoint s (u.biUnion f) := by
    apply Finset.disjoint_left.mpr
    intro z hzs hz
    obtain ⟨x, hx, hz⟩ := Finset.mem_biUnion.mp hz
    have hx' : 1 ≤ x ∧ x ≤ h ∧ x ∉ s := by
      simpa only [u, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hx
    simp only [f, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx'.2.2 hzs
    · exact hx'.2.2 ((hsymm x hx'.1 (by omega)).mpr hzs)
  have hu := hs.union hpair hd
  convert hu using 1
  ext z
  simp only [Finset.mem_union, Finset.mem_biUnion]
  constructor
  · intro hz
    have hz' := Finset.mem_Icc.mp hz
    by_cases hzs : z ∈ s
    · exact Or.inl hzs
    · have hzP : z < P := by
        by_contra hzP
        exact hzs (htop (Finset.mem_Icc.mpr (by omega)))
      apply Or.inr
      by_cases hzh : z ≤ h
      · refine ⟨z, ?_, ?_⟩
        · simp only [u, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hz'.1, hzh⟩, hzs⟩
        · simp [f]
      · refine ⟨P-z, ?_, ?_⟩
        · simp only [u, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨by omega, ?_⟩
          intro hmem
          exact hzs ((hsymm z hz'.1 hzP).mpr hmem)
        · simp only [f, Finset.mem_insert, Finset.mem_singleton]
          exact Or.inr (by omega)
  · rintro (hz | ⟨x, hx, hz⟩)
    · exact hsub hz
    · have hx' : 1 ≤ x ∧ x ≤ h ∧ x ∉ s := by
        simpa only [u, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hx
      simp only [f, Finset.mem_insert, Finset.mem_singleton] at hz
      apply Finset.mem_Icc.mpr
      omega


/-- The contracted low support, expressed without natural subtraction. -/
def criticalSupport (r a : ℤ) : Finset ℤ :=
  insert (r+a) ((Finset.Icc 1 (r-1)).erase a)

@[simp] theorem mem_criticalSupport {r a x : ℤ} :
    x ∈ criticalSupport r a ↔ x = r+a ∨ (1 ≤ x ∧ x < r ∧ x ≠ a) := by
  simp only [criticalSupport, Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
  omega

/-- Translated signed vertices comprise the upper tail and reflected low support. -/
theorem mem_shift_signed {P r a x : ℤ} :
    x ∈ (signedVertices r a).image (fun y => P+y) ↔
      (P+1 ≤ x ∧ x ≤ P+r) ∨ P-x ∈ criticalSupport r a := by
  have he : x ∈ (signedVertices r a).image (fun y => P+y) ↔
      x-P ∈ signedVertices r a := by
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      have heq : y = x-P := by omega
      simpa only [heq] using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x-P, hx, by omega⟩
  rw [he]
  simp only [signedVertices, Finset.mem_union, Finset.mem_singleton,
    mem_neg_image, Finset.mem_erase, Finset.mem_Icc, mem_criticalSupport]
  omega

 theorem criticalSupport_bounds {P r a x : ℤ} (ha : 1 ≤ a) (har : a < r)
    (hPr : 2*r < P) (hx : x ∈ criticalSupport r a) : 1 ≤ x ∧ x < P := by
  rw [mem_criticalSupport] at hx
  omega

/-- A good low support and the signed top suffice once their overlap is repaired. -/
theorem critical_support_completion {P r a : ℤ} {t : ℕ}
    {zs : Finset (Finset ℤ)} {L : Finset ℤ}
    (hP : P = (3 : ℤ)^t) (ha : 1 ≤ a) (har : a < r) (hPr : 2*r < P)
    (hz : ZeroPartition (signedVertices r a) zs) (hL : HasGood L)
    (hLsub : L ⊆ criticalSupport r a)
    (hcover : criticalSupport r a ⊆
      L ∪ (signedVertices r a).image (fun x => P+x))
    (hdisj : Disjoint L ((signedVertices r a).image (fun x => P+x))) :
    HasGood (Finset.Icc 1 (P+r)) := by
  let T := (signedVertices r a).image (fun x => P+x)
  have ht : HasGood T := ⟨_, hz.shift_eq hP⟩
  have hlt : HasGood (L ∪ T) := hL.union ht hdisj
  have hpblock : HasGood ({P} : Finset ℤ) := by
    rw [hP]
    exact (goodBlock_singleton t).hasGood
  have hnotP : P ∉ L ∪ T := by
    intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have := criticalSupport_bounds ha har hPr (hLsub hx)
      omega
    · have hx' := mem_shift_signed.mp hx
      rcases hx' with hx' | hx'
      · omega
      · have := criticalSupport_bounds ha har hPr hx'
        omega
  have hdP : Disjoint (L ∪ T) ({P} : Finset ℤ) := by
    simpa only [Finset.disjoint_singleton_right] using hnotP
  have hgood := hlt.union hpblock hdP
  apply complete_complement_orbits hP (by omega) hgood
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    apply Finset.mem_Icc.mpr
    rcases hx with (hx | hx) | rfl
    · have := criticalSupport_bounds ha har hPr (hLsub hx)
      omega
    · have hx' := mem_shift_signed.mp hx
      rcases hx' with hx' | hx'
      · omega
      · have := criticalSupport_bounds ha har hPr hx'
        omega
    · omega
  · intro x hx
    have hx' := Finset.mem_Icc.mp hx
    by_cases heq : x = P
    · simp [heq]
    · apply Finset.mem_union.mpr
      apply Or.inl
      apply Finset.mem_union.mpr
      apply Or.inr
      apply mem_shift_signed.mpr
      exact Or.inl (by omega)
  · have hmem (x : ℤ) (hx1 : 1 ≤ x) (hxP : x < P) :
        x ∈ L ∪ T ∪ {P} ↔ x ∈ criticalSupport r a ∨ P-x ∈ criticalSupport r a := by
      constructor
      · intro hx
        simp only [Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with (hx | hx) | hx
        · exact Or.inl (hLsub hx)
        · have hx' := mem_shift_signed.mp hx
          rcases hx' with hx' | hx'
          · omega
          · exact Or.inr hx'
        · omega
      · rintro (hx | hx)
        · exact Finset.mem_union.mpr (Or.inl (hcover hx))
        · apply Finset.mem_union.mpr
          apply Or.inl
          apply Finset.mem_union.mpr
          exact Or.inr (mem_shift_signed.mpr (Or.inr hx))
    intro x hx1 hxP
    rw [hmem x hx1 hxP, hmem (P-x) (by omega) (by omega)]
    have heq : P-(P-x) = x := by omega
    rw [heq]
    exact or_comm


 theorem criticalSupport_eq_contractSupport (r : ℕ) (a : ℤ) :
    criticalSupport (r : ℤ) a = contractSupport (interval r) a (r : ℤ) := by
  ext x
  simp only [mem_criticalSupport, contractSupport, Finset.mem_insert,
    Finset.mem_erase, interval, Finset.mem_Icc]
  omega

 theorem eq_pair_of_card_le_two_of_sum {b : Finset ℤ} {d P : ℤ}
    (hd : d ∈ b) (hcard : b.card ≤ 2) (hsum : b.sum id = P) (hne : d ≠ P) :
    b = {d, P-d} := by
  have hpos : 0 < b.card := Finset.card_pos.mpr ⟨d, hd⟩
  have hc2 : b.card = 2 := by
    by_contra hc2
    have hc1 : b.card = 1 := by omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc1
    simp only [Finset.mem_singleton] at hd
    subst x
    exact hne (by simpa using hsum)
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc2
  have hs : x+y = P := by simpa [hxy] using hsum
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

 theorem contractBlock_sum {b : Finset ℤ} {a r : ℤ}
    (ha : a ∈ b) (hr : r ∈ b) (har : a ≠ r) (hd : a+r ∉ b) :
    (contractBlock b a r).sum id = b.sum id := by
  have hra : r ∈ b.erase a := Finset.mem_erase.mpr ⟨Ne.symm har, hr⟩
  have hda : a+r ∉ (b.erase a).erase r := by
    intro h
    exact hd (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have h1 := Finset.sum_erase_add (s := b) (f := id) ha
  have h2 := Finset.sum_erase_add (s := b.erase a) (f := id) hra
  simp only [contractBlock, Finset.sum_insert hda, id_eq]
  simp only [id_eq] at h1 h2
  omega

/-- Any low/high overlap forces precisely the contracted complementary pair. -/
theorem contractBlock_eq_collision_pair {r : ℕ} {P a : ℤ} {t : ℕ}
    {bs : Finset (Finset ℤ)} {b : Finset ℤ}
    (hs : GoodOn (interval r) bs) (hb : b ∈ bs)
    (ha : a ∈ b) (hr : (r : ℤ) ∈ b) (har : a ≠ (r : ℤ))
    (hP : P = (3 : ℤ)^t) (hPr : 2*(r : ℤ) < P)
    (hc : P-((r : ℤ)+a) ∈ criticalSupport (r : ℤ) a) :
    contractBlock b a (r : ℤ) = {(r : ℤ)+a, P-((r : ℤ)+a)} := by
  have hab : 1 ≤ a ∧ a ≤ (r : ℤ) := by
    simpa only [interval, Finset.mem_Icc] using hs.subset hb ha
  have haltr : a < (r : ℤ) := by omega
  have hdnot : a+(r : ℤ) ∉ b := by
    intro hd
    have hd' : 1 ≤ a+(r : ℤ) ∧ a+(r : ℤ) ≤ (r : ℤ) := by
      simpa only [interval, Finset.mem_Icc] using hs.subset hb hd
    omega
  have hsumge : a+(r : ℤ) ≤ b.sum id := by
    have hsub : ({a, (r : ℤ)} : Finset ℤ) ⊆ b := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := (id : ℤ → ℤ)) hsub
      (by
        intro x hx _
        have hx' : 1 ≤ x ∧ x ≤ (r : ℤ) := by
          simpa only [interval, Finset.mem_Icc] using hs.subset hb hx
        dsimp
        omega)
    simpa [har] using h
  obtain ⟨u, hu⟩ := (hs.block hb).2.2
  have hsumhi := (hs.block_sum_bounds hb).2
  have hclow := mem_criticalSupport.mp hc
  have hsumeq : b.sum id = P :=
    power_three_between hP hu (by omega) (by omega)
  have hcontract := contractBlock_good (hs.block hb) ha hr har hdnot
  apply eq_pair_of_card_le_two_of_sum
  · simp [contractBlock, add_comm]
  · exact hcontract.2
  · exact (contractBlock_sum ha hr har hdnot).trans hsumeq
  · omega


/-- Transfer an actual source partition and actual signed frame to the critical target. -/
theorem critical_transfer {P r t : ℕ} {a : ℤ}
    {bs zs : Finset (Finset ℤ)} {b : Finset ℤ}
    (hP : P = 3^t) (hPr : 2*r < P)
    (hs : GoodOn (interval r) bs) (hb : b ∈ bs)
    (ha : a ∈ b) (hr : (r : ℤ) ∈ b) (har : a ≠ (r : ℤ))
    (hz : ZeroPartition (signedVertices (r : ℤ) a) zs) :
    HasGood (interval (P+r)) := by
  have hP' : (P : ℤ) = (3 : ℤ)^t := by exact_mod_cast hP
  have hPr' : 2*(r : ℤ) < (P : ℤ) := by exact_mod_cast hPr
  have hab : 1 ≤ a ∧ a ≤ (r : ℤ) := by
    simpa only [interval, Finset.mem_Icc] using hs.subset hb ha
  have haltr : a < (r : ℤ) := by omega
  have hdnot : a+(r : ℤ) ∉ interval r := by
    simp only [interval, Finset.mem_Icc]
    omega
  have hDc : GoodOn (criticalSupport (r : ℤ) a)
      (insert (contractBlock b a (r : ℤ)) (bs.erase b)) := by
    rw [criticalSupport_eq_contractSupport]
    exact hs.contract hb ha hr har hdnot
  suffices h : HasGood (Finset.Icc 1 ((P : ℤ)+(r : ℤ))) by
    simpa only [interval, Nat.cast_add] using h
  by_cases hc : (P : ℤ)-((r : ℤ)+a) ∈ criticalSupport (r : ℤ) a
  · have hbeq := contractBlock_eq_collision_pair hs hb ha hr har hP' hPr' hc
    have hpairmem : ({(r : ℤ)+a, (P : ℤ)-((r : ℤ)+a)} : Finset ℤ) ∈
        insert (contractBlock b a (r : ℤ)) (bs.erase b) := by
      rw [← hbeq]
      exact Finset.mem_insert_self _ _
    have hDel := hDc.erase hpairmem
    apply critical_support_completion hP' hab.1 haltr hPr' hz ⟨_, hDel⟩
      Finset.sdiff_subset
    · intro x hx
      by_cases hxp : x ∈ ({(r : ℤ)+a, (P : ℤ)-((r : ℤ)+a)} : Finset ℤ)
      · apply Finset.mem_union.mpr
        apply Or.inr
        apply mem_shift_signed.mpr
        apply Or.inr
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
      have hxavoid : x ≠ (r : ℤ)+a ∧ x ≠ (P : ℤ)-((r : ℤ)+a) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hxL.2
      have hxt := mem_shift_signed.mp hx'
      rcases hxt with hxt | hxt
      · omega
      · rw [mem_criticalSupport] at hxt
        omega
  · apply critical_support_completion hP' hab.1 haltr hPr' hz ⟨_, hDc⟩
      (Finset.Subset.refl _)
    · intro x hx
      exact Finset.mem_union.mpr (Or.inl hx)
    · apply Finset.disjoint_left.mpr
      intro x hx hx'
      rw [mem_criticalSupport] at hx hc
      have hxt := mem_shift_signed.mp hx'
      rcases hxt with hxt | hxt
      · omega
      · rw [mem_criticalSupport] at hxt
        omega


/-- Existence of the required signed frames suffices for every critical induction step. -/
theorem critical_extension_of_frames {P r t : ℕ}
    (hP : P = 3^t) (hPr : 2*r < P) (hmod : r % 3 = 2)
    (hs : HasGood (interval r))
    (hframes : ∀ a : ℤ, 1 ≤ a → a < (r : ℤ) → ¬ (3 : ℤ) ∣ a →
      ∃ zs, ZeroPartition (signedVertices (r : ℤ) a) zs) :
    HasGood (interval (P+r)) := by
  obtain ⟨bs, hbs⟩ := hs
  obtain ⟨b, hb, hr, a, ha, har, ha3⟩ := hbs.maximum_partner (by omega) hmod
  have hab : 1 ≤ a ∧ a ≤ (r : ℤ) := by
    simpa only [interval, Finset.mem_Icc] using hbs.subset hb ha
  obtain ⟨zs, hzs⟩ := hframes a hab.1 (by omega) ha3
  exact critical_transfer hP hPr hbs hb ha hr har hzs

end
end GN

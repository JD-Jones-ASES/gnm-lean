import GN.Basic

namespace GN
noncomputable section

/-- Replace two distinct members of a block by their sum. -/
def contractBlock (b : Finset ℤ) (a r : ℤ) : Finset ℤ :=
  insert (a+r) ((b.erase a).erase r)

/-- Contraction changes the ground set by the same replacement. -/
def contractSupport (s : Finset ℤ) (a r : ℤ) : Finset ℤ :=
  insert (a+r) ((s.erase a).erase r)

lemma contractBlock_good {b : Finset ℤ} {a r : ℤ} (hb : GoodBlock b)
    (ha : a ∈ b) (hr : r ∈ b) (har : a ≠ r) (hd : a+r ∉ b) :
    GoodBlock (contractBlock b a r) ∧ (contractBlock b a r).card ≤ 2 := by
  have hra : r ∈ b.erase a := Finset.mem_erase.mpr ⟨Ne.symm har, hr⟩
  have hda : a+r ∉ (b.erase a).erase r := by
    intro h
    exact hd (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hc : (contractBlock b a r).card ≤ 2 := by
    simp only [contractBlock, Finset.card_insert_of_notMem hda,
      Finset.card_erase_of_mem hra, Finset.card_erase_of_mem ha]
    have := hb.2.1
    omega
  have hs : (contractBlock b a r).sum id = b.sum id := by
    have h1 := Finset.sum_erase_add (s := b) (f := id) ha
    have h2 := Finset.sum_erase_add (s := b.erase a) (f := id) hra
    simp only [contractBlock, Finset.sum_insert hda, id_eq]
    simp only [id_eq] at h1 h2
    omega
  refine ⟨⟨by simp [contractBlock], by omega, ?_⟩, hc⟩
  obtain ⟨k, hk⟩ := hb.2.2
  exact ⟨k, hs.trans hk⟩

lemma GoodOn.contract {s : Finset ℤ} {bs : Finset (Finset ℤ)}
    (hs : GoodOn s bs) {b : Finset ℤ} (hb : b ∈ bs) {a r : ℤ}
    (ha : a ∈ b) (hr : r ∈ b) (har : a ≠ r) (hd : a+r ∉ s) :
    GoodOn (contractSupport s a r) (insert (contractBlock b a r) (bs.erase b)) := by
  have hdb : a+r ∉ b := fun h => hd (hs.subset hb h)
  have hgood := (contractBlock_good (hs.block hb) ha hr har hdb).1
  have hother (c : Finset ℤ) (hc : c ∈ bs.erase b) : a ∉ c ∧ r ∉ c := by
    have hcbs := Finset.mem_of_mem_erase hc
    have hcb := (Finset.mem_erase.mp hc).1
    have hdcb := hs.2.1 c hcbs b hb hcb
    exact ⟨fun h => Finset.disjoint_left.mp hdcb h ha,
      fun h => Finset.disjoint_left.mp hdcb h hr⟩
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase,
      contractSupport, contractBlock]
    constructor
    · rintro ⟨c, hc, hx⟩
      rcases hc with rfl | ⟨hcb, hc⟩
      · rcases Finset.mem_insert.mp hx with hxd | hx
        · exact Or.inl hxd
        · exact Or.inr ⟨(Finset.mem_erase.mp hx).1,
            (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1,
            hs.subset hb (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))⟩
      · have havoid := hother c (Finset.mem_erase.mpr ⟨hcb, hc⟩)
        exact Or.inr ⟨fun h => havoid.2 (h ▸ hx), fun h => havoid.1 (h ▸ hx),
          hs.subset hc hx⟩
    · intro hx
      rcases hx with hxd | ⟨hxr, hxa, hxs⟩
      · refine ⟨contractBlock b a r, Or.inl rfl, ?_⟩
        exact Finset.mem_insert.mpr (Or.inl hxd)
      · have hxu : x ∈ bs.biUnion id := hs.1.symm ▸ hxs
        obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hxu
        by_cases hcb : c = b
        · subst c
          refine ⟨contractBlock b a r, Or.inl rfl, ?_⟩
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
            ⟨hxr, Finset.mem_erase.mpr ⟨hxa, hxc⟩⟩))
        · exact ⟨c, Or.inr ⟨hcb, hc⟩, hxc⟩
  · intro c hc e he hce
    rcases Finset.mem_insert.mp hc with rfl | hc <;>
      rcases Finset.mem_insert.mp he with rfl | he
    · exact (hce rfl).elim
    · apply Finset.disjoint_left.mpr
      intro x hx hxe
      rcases Finset.mem_insert.mp hx with hxd | hx
      · exact hd (hxd ▸ hs.subset (Finset.mem_of_mem_erase he) hxe)
      · exact Finset.disjoint_left.mp
          (hs.2.1 b hb e (Finset.mem_of_mem_erase he)
            (Ne.symm (Finset.mem_erase.mp he).1))
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)) hxe
    · apply Finset.disjoint_left.mpr
      intro x hxc hx
      rcases Finset.mem_insert.mp hx with hxd | hx
      · exact hd (hxd ▸ hs.subset (Finset.mem_of_mem_erase hc) hxc)
      · exact Finset.disjoint_left.mp
          (hs.2.1 c (Finset.mem_of_mem_erase hc) b hb
            (Finset.mem_erase.mp hc).1) hxc
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    · exact hs.2.1 c (Finset.mem_of_mem_erase hc) e (Finset.mem_of_mem_erase he) hce
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hgood
    · exact hs.block (Finset.mem_of_mem_erase hc)


lemma GoodOn.erase {s : Finset ℤ} {bs : Finset (Finset ℤ)}
    (hs : GoodOn s bs) {b : Finset ℤ} (hb : b ∈ bs) :
    GoodOn (s \ b) (bs.erase b) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
      refine Finset.mem_sdiff.mpr ⟨hs.subset (Finset.mem_of_mem_erase hc) hxc, ?_⟩
      intro hxb
      exact Finset.disjoint_left.mp
        (hs.2.1 c (Finset.mem_of_mem_erase hc) b hb (Finset.mem_erase.mp hc).1) hxc hxb
    · intro hx
      obtain ⟨hxs, hxb⟩ := Finset.mem_sdiff.mp hx
      have hxu : x ∈ bs.biUnion id := hs.1.symm ▸ hxs
      obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hxu
      exact Finset.mem_biUnion.mpr ⟨c,
        Finset.mem_erase.mpr ⟨fun h => hxb (h ▸ hxc), hc⟩, hxc⟩
  · intro c hc e he hce
    exact hs.2.1 c (Finset.mem_of_mem_erase hc) e (Finset.mem_of_mem_erase he) hce
  · intro c hc
    exact hs.block (Finset.mem_of_mem_erase hc)

lemma power_three_between {P q : ℤ} {t u : ℕ}
    (hp : P = 3^t) (hq : q = 3^u) (hlo : P < 3*q) (hhi : q < 3*P) : q = P := by
  subst P q
  have heq : u = t := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hut | hut
    · have hpow : (3:ℤ)^(u+1) ≤ 3^t := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_succ] at hpow
      nlinarith
    · have hpow : (3:ℤ)^(t+1) ≤ 3^u := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_succ] at hpow
      nlinarith
  rw [heq]

lemma GoodOn.block_sum_bounds {r : ℕ} {bs : Finset (Finset ℤ)}
    (hs : GoodOn (interval r) bs) {b : Finset ℤ} (hb : b ∈ bs) :
    0 < b.sum id ∧ b.sum id ≤ 3*(r:ℤ) := by
  have hgood := hs.block hb
  have hbounds (x : ℤ) (hx : x ∈ b) : 1 ≤ x ∧ x ≤ (r:ℤ) := by
    simpa [interval] using hs.subset hb hx
  obtain ⟨k, hk⟩ := hgood.2.2
  refine ⟨hk ▸ pow_pos (by norm_num) k, ?_⟩
  calc
    b.sum id ≤ ∑ _x ∈ b, (r:ℤ) := Finset.sum_le_sum (fun x hx => (hbounds x hx).2)
    _ = (b.card:ℤ)*(r:ℤ) := by simp
    _ ≤ 3*(r:ℤ) := by exact mul_le_mul_of_nonneg_right (by exact_mod_cast hgood.2.1) (by positivity)

lemma GoodOn.maximum_partner {r : ℕ} {bs : Finset (Finset ℤ)}
    (hs : GoodOn (interval r) bs) (hr : 2 ≤ r) (hmod : r % 3 = 2) :
    ∃ b ∈ bs, (r:ℤ) ∈ b ∧ ∃ a ∈ b, a ≠ (r:ℤ) ∧ ¬ (3:ℤ) ∣ a := by
  have hrmem : (r:ℤ) ∈ interval r := by simp [interval]; omega
  have hru : (r:ℤ) ∈ bs.biUnion id := hs.1.symm ▸ hrmem
  obtain ⟨b, hb, hrb⟩ := Finset.mem_biUnion.mp hru
  refine ⟨b, hb, hrb, ?_⟩
  obtain ⟨k, hk⟩ := (hs.block hb).2.2
  have hle : (r:ℤ) ≤ b.sum id := by
    apply Finset.single_le_sum (f := id) _ hrb
    intro x hx
    have := hs.subset hb hx
    simp only [interval, Finset.mem_Icc] at this
    dsimp
    omega
  have hkpos : 0 < k := by
    by_contra hz
    have : k = 0 := by omega
    subst k
    simp only [pow_zero] at hk
    rw [hk] at hle
    omega
  have hsumdiv : (3:ℤ) ∣ b.sum id := by
    rw [hk]
    exact dvd_pow_self 3 (by omega)
  by_contra hnone
  push Not at hnone
  have herase : (3:ℤ) ∣ (b.erase (r:ℤ)).sum id := by
    apply Finset.dvd_sum
    intro a ha
    exact hnone a (Finset.mem_of_mem_erase ha) (Finset.mem_erase.mp ha).1
  have heq : (b.erase (r:ℤ)).sum id + (r:ℤ) = b.sum id :=
    Finset.sum_erase_add (s := b) (f := id) hrb
  have hrdiv : (3:ℤ) ∣ (r:ℤ) := by
    have h := dvd_sub hsumdiv herase
    have heqr : b.sum id - (b.erase (r:ℤ)).sum id = (r:ℤ) := by omega
    rwa [heqr] at h
  have hnat : 3 ∣ r := by exact_mod_cast hrdiv
  have := Nat.mod_eq_zero_of_dvd hnat
  omega

end
end GN

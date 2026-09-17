import GN.Signed

namespace GN
noncomputable section

/-- Doubling modulo the odd integer 2m+1, represented on the interval [1,2m]. -/
def doubling (m x : ℤ) : ℤ :=
  if x ≤ m then 2*x else 2*x-(2*m+1)

/-- The explicit doubling map permutes the interval [1,2m]. -/
theorem doubling_bijOn (m : ℤ) (hm : 0 ≤ m) :
    Set.BijOn (doubling m) (Finset.Icc 1 (2*m)) (Finset.Icc 1 (2*m)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : 1 ≤ x ∧ x ≤ 2*m := by simpa only [Finset.mem_coe, Finset.mem_Icc] using hx
    simp only [Finset.mem_coe, Finset.mem_Icc, doubling]
    split_ifs <;> omega
  · intro x hx y hy hxy
    have hx' : 1 ≤ x ∧ x ≤ 2*m := by simpa only [Finset.mem_coe, Finset.mem_Icc] using hx
    have hy' : 1 ≤ y ∧ y ≤ 2*m := by simpa only [Finset.mem_coe, Finset.mem_Icc] using hy
    simp only [doubling] at hxy
    split_ifs at hxy <;> omega
  · intro y hy
    have hy' : 1 ≤ y ∧ y ≤ 2*m := by simpa only [Finset.mem_coe, Finset.mem_Icc] using hy
    by_cases hparity : y % 2 = 0
    · refine ⟨y/2, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_Icc]
        omega
      · simp only [doubling]
        split_ifs <;> omega
    · refine ⟨(y+2*m+1)/2, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_Icc]
        omega
      · simp only [doubling]
        split_ifs <;> omega

/-- The doubling displacements use every nonzero value from -m through m once. -/
theorem doubling_displacement_bijOn (m : ℤ) (hm : 0 ≤ m) :
    Set.BijOn (fun x => doubling m x-x) (Finset.Icc 1 (2*m))
      ((Finset.Icc (-m) m).erase 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : 1 ≤ x ∧ x ≤ 2*m := by simpa only [Finset.mem_coe, Finset.mem_Icc] using hx
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_Icc, doubling]
    split_ifs <;> omega
  · intro x hx y hy hxy
    have hx' : 1 ≤ x ∧ x ≤ 2*m := by simpa only [Finset.mem_coe, Finset.mem_Icc] using hx
    have hy' : 1 ≤ y ∧ y ≤ 2*m := by simpa only [Finset.mem_coe, Finset.mem_Icc] using hy
    dsimp only at hxy
    simp only [doubling] at hxy
    split_ifs at hxy <;> omega
  · intro y hy
    have hy' : y ≠ 0 ∧ -m ≤ y ∧ y ≤ m := by
      simpa only [Finset.mem_coe, Finset.mem_erase, Finset.mem_Icc] using hy
    by_cases hypos : 0 < y
    · refine ⟨y, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_Icc]
        omega
      · simp only [doubling]
        split_ifs <;> omega
    · refine ⟨y+2*m+1, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_Icc]
        omega
      · simp only [doubling]
        split_ifs <;> omega

/-- An unconditional displacement permutation on an interval of even size. -/
theorem exists_doubling_permutation (m : ℤ) (hm : 0 ≤ m) :
    ∃ σ : ℤ → ℤ,
      Set.BijOn σ (Finset.Icc 1 (2*m)) (Finset.Icc 1 (2*m)) ∧
      Set.BijOn (fun x => σ x-x) (Finset.Icc 1 (2*m))
        ((Finset.Icc (-m) m).erase 0) :=
  ⟨doubling m, doubling_bijOn m hm, doubling_displacement_bijOn m hm⟩


/-- Translate the even-interval construction to any identical endpoint-hole domain. -/
theorem displacement_of_doubling_translation {k j c : ℤ} (hk : 0 ≤ k)
    (hdom : ∀ x : ℤ, x ∈ displacementDomain k j ↔
      x+c ∈ Finset.Icc 1 (2*k)) :
    DisplacementPermutation k j (fun x => doubling k (x+c)-c) := by
  have hσ := doubling_bijOn k hk
  have hδ := doubling_displacement_bijOn k hk
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply (hdom _).mpr
      have hx' := hσ.mapsTo ((hdom x).mp hx)
      simpa only [sub_add_cancel, Finset.mem_coe] using hx'
    · intro x hx y hy hxy
      have heq : doubling k (x+c) = doubling k (y+c) := by
        dsimp only at hxy
        omega
      have hxy' := hσ.injOn ((hdom x).mp hx) ((hdom y).mp hy) heq
      omega
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hσ.surjOn ((hdom y).mp hy)
      refine ⟨x-c, (hdom _).mpr ?_, ?_⟩
      · simpa only [sub_add_cancel, Finset.mem_coe] using hx
      · simp only [sub_add_cancel]
        omega
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hx' := hδ.mapsTo ((hdom x).mp hx)
      have heq : doubling k (x+c)-c-x = doubling k (x+c)-(x+c) := by ring
      dsimp only
      rw [heq]
      exact hx'
    · intro x hx y hy hxy
      have heq : doubling k (x+c)-(x+c) = doubling k (y+c)-(y+c) := by
        dsimp only at hxy
        omega
      have hxy' := hδ.injOn ((hdom x).mp hx) ((hdom y).mp hy) heq
      omega
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hδ.surjOn hy
      refine ⟨x-c, (hdom _).mpr ?_, ?_⟩
      · simpa only [sub_add_cancel, Finset.mem_coe] using hx
      · dsimp only at hxy ⊢
        simp only [sub_add_cancel]
        omega

/-- Unconditional endpoint-hole permutation with the left endpoint removed. -/
theorem doubling_left_endpoint (k : ℤ) (hk : 0 ≤ k) :
    DisplacementPermutation k (-k) (fun x => doubling k (x+k)-k) := by
  apply displacement_of_doubling_translation hk
  intro x
  simp only [mem_displacementDomain, Finset.mem_Icc]
  omega

/-- Unconditional endpoint-hole permutation with the right endpoint removed. -/
theorem doubling_right_endpoint (k : ℤ) (hk : 0 ≤ k) :
    DisplacementPermutation k k (fun x => doubling k (x+(k+1))-(k+1)) := by
  apply displacement_of_doubling_translation hk
  intro x
  simp only [mem_displacementDomain, Finset.mem_Icc]
  omega

 theorem exists_endpoint_displacement (k : ℤ) (hk : 0 ≤ k) (j : ℤ)
    (hj : j = -k ∨ j = k) : ∃ σ : ℤ → ℤ, DisplacementPermutation k j σ := by
  rcases hj with hj | hj
  · rw [hj]
    exact ⟨_, doubling_left_endpoint k hk⟩
  · rw [hj]
    exact ⟨_, doubling_right_endpoint k hk⟩

end
end GN

import GN.PermutationGlue
import GN.Minimal

namespace GN
noncomputable section

/-- Uniform existence for one excess above minimal Langford order.
The defect threshold and the required hole parity are explicit parameters. -/
def LangfordFamily (minDefect i : ℤ) (parity : ℤ → ℤ) : Prop :=
  ∀ d : ℤ, minDefect ≤ d → ∀ h : ℤ,
    (1 ≤ h ∧ h ≤ 4*d+2*i-1) → h%2 = (parity d)%2 →
    ∃ ps, LangfordPairing d (3*d-2+i) h ps

 theorem LangfordFamily.mono {a b i : ℤ} {p : ℤ → ℤ}
    (h : LangfordFamily a i p) (hab : a ≤ b) : LangfordFamily b i p := by
  intro d hd q hq hp
  exact h d (hab.trans hd) q hq hp

 theorem minimal_langford_family : LangfordFamily 1 0 (fun _ => 1) := by
  intro d hd h hh hp
  dsimp only at hp
  simpa only [add_zero] using
    exists_minimal_langford (d := d) (h := h) hd (by omega) (by omega)

/-- Two Langford families with opposite hole parities cover a suffix position.
Their defects differ by two, so the two prefix lengths differ by four. -/
theorem permutation_from_opposite_pairings {d k H p : ℤ}
    (_hd : 3 ≤ d) (hH : 2*d-1 ≤ H ∧ H ≤ 2*k+1)
    (hlow : ∀ h : ℤ, (1 ≤ h ∧ h ≤ 2*(k-d+1)+1) → h%2 = p%2 →
      ∃ ps, LangfordPairing d k h ps)
    (hhigh : ∀ h : ℤ, (1 ≤ h ∧ h ≤ 2*(k-(d-2)+1)+1) → h%2 = (p+1)%2 →
      ∃ ps, LangfordPairing (d-2) k h ps) :
    ∃ σ : ℤ → ℤ, PermutationWithDifferences
      ((Finset.Icc 1 (2*k+1)).erase H) ((Finset.Icc (-k) k).erase 0) σ := by
  let h := H-2*(d-1)
  by_cases hp : h%2 = p%2
  · obtain ⟨ps, hps⟩ := hlow h (by dsimp [h]; omega) hp
    obtain ⟨σ, hσ⟩ := hps.with_doubling_prefix
    have he : h+2*(d-1) = H := by dsimp [h]; ring
    rw [he] at hσ
    exact ⟨σ, hσ⟩
  · obtain ⟨ps, hps⟩ := hhigh (h+4) (by dsimp [h]; omega) (by omega)
    obtain ⟨σ, hσ⟩ := hps.with_doubling_prefix
    have he : h+4+2*(d-2-1) = H := by dsimp [h]; ring
    rw [he] at hσ
    exact ⟨σ, hσ⟩

/-- The six explicit excess families cover every upper-half position for k≥22. -/
theorem high_position_permutation_of_langford_families
    (E0 : LangfordFamily 8 0 (fun _ => 1))
    (E1 : LangfordFamily 8 1 (fun d => d+1))
    (E2 : LangfordFamily 8 2 (fun _ => 0))
    (E6 : LangfordFamily 6 6 (fun _ => 0))
    (E7 : LangfordFamily 6 7 (fun d => d))
    (E8 : LangfordFamily 6 8 (fun _ => 1))
    {k H : ℤ} (hk : 22 ≤ k) (hH : k+1 ≤ H ∧ H ≤ 2*k+1) :
    ∃ σ : ℤ → ℤ, PermutationWithDifferences
      ((Finset.Icc 1 (2*k+1)).erase H) ((Finset.Icc (-k) k).erase 0) σ := by
  let d := (k+2)/3
  have hd : 8 ≤ d := by dsimp [d]; omega
  have hi : k = 3*d-2 ∨ k = 3*d-1 ∨ k = 3*d := by dsimp [d]; omega
  have hbound : 2*d-1 ≤ H ∧ H ≤ 2*k+1 := by omega
  rcases hi with hi | hi | hi
  · apply permutation_from_opposite_pairings (d := d) (p := 1) (by omega) hbound
    · intro h hh hp
      obtain ⟨ps, hps⟩ := E0 d hd h (by omega) (by omega)
      have he : 3*d-2+0 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
    · intro h hh hp
      obtain ⟨ps, hps⟩ := E6 (d-2) (by omega) h (by omega) (by dsimp only; omega)
      have he : 3*(d-2)-2+6 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
  · apply permutation_from_opposite_pairings (d := d) (p := d+1) (by omega) hbound
    · intro h hh hp
      obtain ⟨ps, hps⟩ := E1 d hd h (by omega) hp
      have he : 3*d-2+1 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
    · intro h hh hp
      obtain ⟨ps, hps⟩ := E7 (d-2) (by omega) h (by omega) (by dsimp only; omega)
      have he : 3*(d-2)-2+7 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
  · apply permutation_from_opposite_pairings (d := d) (p := 0) (by omega) hbound
    · intro h hh hp
      obtain ⟨ps, hps⟩ := E2 d hd h (by omega) hp
      have he : 3*d-2+2 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩
    · intro h hh hp
      obtain ⟨ps, hps⟩ := E8 (d-2) (by omega) h (by omega) (by dsimp only; omega)
      have he : 3*(d-2)-2+8 = k := by omega
      rw [he] at hps
      exact ⟨ps, hps⟩

/-- Reflection and centering give all prescribed holes, conditional precisely on
six explicitly stated Langford-family existence hypotheses. -/
theorem displacement_permutations_of_langford_families
    (E0 : LangfordFamily 8 0 (fun _ => 1))
    (E1 : LangfordFamily 8 1 (fun d => d+1))
    (E2 : LangfordFamily 8 2 (fun _ => 0))
    (E6 : LangfordFamily 6 6 (fun _ => 0))
    (E7 : LangfordFamily 6 7 (fun d => d))
    (E8 : LangfordFamily 6 8 (fun _ => 1))
    {k j : ℤ} (hk : 22 ≤ k) (hj : -k ≤ j ∧ j ≤ k) :
    ∃ σ : ℤ → ℤ, DisplacementPermutation k j σ := by
  let H := j+k+1
  have hb : 1 ≤ H ∧ H ≤ 2*k+1 := by dsimp [H]; omega
  have hp : ∃ σ : ℤ → ℤ, PermutationWithDifferences
      ((Finset.Icc 1 (2*k+1)).erase H) ((Finset.Icc (-k) k).erase 0) σ := by
    by_cases hh : k+1 ≤ H
    · exact high_position_permutation_of_langford_families E0 E1 E2 E6 E7 E8 hk ⟨hh,hb.2⟩
    · obtain ⟨σ, hσ⟩ := high_position_permutation_of_langford_families
        E0 E1 E2 E6 E7 E8 hk (H := 2*k+2-H) (by omega)
      have hr := hσ.reflect_positions
      have he : 2*k+2-(2*k+2-H) = H := by ring
      rw [he] at hr
      exact ⟨_, hr⟩
  obtain ⟨σ, hσ⟩ := hp
  have hc := hσ.to_centered
  have he : H-k-1 = j := by dsimp [H]; ring
  rw [he] at hc
  exact ⟨_, hc⟩

end
end GN

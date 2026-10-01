import Mathlib

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators

/-- **Separated extraction.**  Every finite set `S` of complex numbers contains a subset `R`
which is `1`-separated in the imaginary part, such that every element of `S` lies within
imaginary distance `1` of an element of `R`. -/
theorem existsSeparatedCover (S : Finset ℂ) :
    ∃ R : Finset ℂ, R ⊆ S ∧
      (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) ∧
      (∀ z ∈ S, ∃ z' ∈ R, |z.im - z'.im| ≤ 1) := by
  classical
  -- Greedy extraction, by strong induction on the finite set (strict subset order).
  refine Finset.strongInductionOn S ?_
  intro S IH
  by_cases hne : S.Nonempty
  · obtain ⟨z0, hz0S⟩ := hne
    -- Keep only the points farther than `1` in imaginary part from `z0`.
    set S' := S.filter (fun z => 1 < |z.im - z0.im|) with hS'def
    have hmemS' : ∀ w, w ∈ S' ↔ w ∈ S ∧ 1 < |w.im - z0.im| := by
      intro w; rw [hS'def, Finset.mem_filter]
    have hS'sub : S' ⊂ S := by
      rw [hS'def, Finset.filter_ssubset]
      exact ⟨z0, hz0S, by rw [sub_self, abs_zero]; norm_num⟩
    obtain ⟨R', hR'sub, hR'sep, hR'cov⟩ := IH S' hS'sub
    have hS'sub_le : S' ⊆ S := fun w hw => ((hmemS' w).mp hw).1
    refine ⟨insert z0 R', ?_, ?_, ?_⟩
    · -- `R ⊆ S`
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hzR
      · exact hz0S
      · exact hS'sub_le (hR'sub hzR)
    · -- separation
      intro z hz z' hz' hne'
      rw [Finset.mem_insert] at hz hz'
      have hz0sep : ∀ w ∈ R', 1 ≤ |z0.im - w.im| := by
        intro w hw
        have : 1 < |w.im - z0.im| := ((hmemS' w).mp (hR'sub hw)).2
        rw [abs_sub_comm] at this
        exact le_of_lt this
      rcases hz with rfl | hzR
      · rcases hz' with rfl | hz'R
        · exact absurd rfl hne'
        · exact hz0sep z' hz'R
      · rcases hz' with rfl | hz'R
        · have := hz0sep z hzR
          rw [abs_sub_comm] at this
          exact this
        · exact hR'sep z hzR z' hz'R hne'
    · -- covering
      intro z hzS
      by_cases hzmem : z ∈ S'
      · obtain ⟨z', hz'R, hle⟩ := hR'cov z hzmem
        exact ⟨z', Finset.mem_insert.mpr (Or.inr hz'R), hle⟩
      · refine ⟨z0, Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
        have hlt : ¬ (1 < |z.im - z0.im|) := fun h => hzmem ((hmemS' z).mpr ⟨hzS, h⟩)
        exact not_lt.mp hlt
  · -- empty case
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    exact ⟨∅, by simp, by simp, by simp⟩

end Work.ZeroDensity.Ingham

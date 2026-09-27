import Mathlib
import Submission.Work.EQ.CycleDefs

namespace Work.EQ.Ladf

/-- Every point of the closed annulus `Ann r₁ r₂` is a limit of points of the open
annulus `{z | max r₁ 0 < ‖z‖ ∧ ‖z‖ < r₂}`. The inner boundary is handled by the fact that
when `max r₁ 0 = 0` the origin itself is a limit of the punctured open annulus; the outer
boundary is reached by scaling towards the origin. -/
theorem Ann_subset_closure_openAnnulus {r₁ r₂ : ℝ} (hr : r₁ < r₂) (h₂ : 0 < r₂) :
    Work.EQ.Ann r₁ r₂ ⊆ closure {z : ℂ | max r₁ 0 < ‖z‖ ∧ ‖z‖ < r₂} := by
  intro z hz
  simp only [Work.EQ.Ann, Set.mem_ofPred_eq] at hz
  obtain ⟨h1, h2⟩ := hz
  have hm : max r₁ 0 < r₂ := max_lt hr h₂
  have hmt : max r₁ 0 ≤ ‖z‖ := max_le h1 (norm_nonneg z)
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases ht : ‖z‖ = 0
  · -- `z = 0`, the inner radius is `0`, and the origin is a limit point.
    have hz0 : z = 0 := norm_eq_zero.mp ht
    have hm0 : max r₁ 0 = 0 := le_antisymm (ht ▸ hmt) (le_max_right _ _)
    set c : ℝ := min r₂ ε / 2 with hc_def
    have hc_pos : 0 < c := by
      rw [hc_def]; have := lt_min h₂ hε; linarith
    have hc_lt_r2 : c < r₂ := by
      rw [hc_def]; have := min_le_left r₂ ε; linarith
    have hc_lt_eps : c < ε := by
      rw [hc_def]; have := min_le_right r₂ ε; linarith
    have hcnorm : ‖(c : ℂ)‖ = c := by simp [abs_of_pos hc_pos]
    refine ⟨(c : ℂ), ?_, ?_⟩
    · rw [Set.mem_ofPred_eq, hm0, hcnorm]; exact ⟨hc_pos, hc_lt_r2⟩
    · rw [hz0, dist_eq_norm, zero_sub, norm_neg, hcnorm]; exact hc_lt_eps
  · -- `z ≠ 0`: scale `z` so that its norm becomes a nearby radius `s ∈ (max r₁ 0, r₂)`.
    have ht_pos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm ht)
    have htm : ‖z‖ ∈ closure (Set.Ioo (max r₁ 0) r₂) := by
      rw [closure_Ioo (ne_of_lt hm)]
      exact ⟨hmt, h2⟩
    rw [Metric.mem_closure_iff] at htm
    obtain ⟨s, hs, hsd⟩ := htm ε hε
    obtain ⟨hms, hsr⟩ := hs
    have hs_pos : 0 < s := lt_of_le_of_lt (le_max_right _ _) hms
    refine ⟨(s / ‖z‖) • z, ?_, ?_⟩
    · rw [Set.mem_ofPred_eq]
      have hnorm : ‖(s / ‖z‖) • z‖ = s := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hs_pos ht_pos)]
        field_simp
      rw [hnorm]
      exact ⟨hms, hsr⟩
    · have hdist : dist z ((s / ‖z‖) • z) = |s - ‖z‖| := by
        rw [dist_eq_norm]
        have h1 : z - (s / ‖z‖) • z = (1 - s / ‖z‖) • z := by rw [sub_smul, one_smul]
        rw [h1, norm_smul, Real.norm_eq_abs]
        have haux : |1 - s / ‖z‖| * ‖z‖ = |s - ‖z‖| := by
          have h : |1 - s / ‖z‖| * ‖z‖ = |(1 - s / ‖z‖) * ‖z‖| := by
            rw [abs_mul, abs_of_pos ht_pos]
          rw [h, abs_sub_comm]
          congr 1
          field_simp
        exact haux
      rw [hdist]
      rw [Real.dist_eq, abs_sub_comm] at hsd
      exact hsd

end Work.EQ.Ladf

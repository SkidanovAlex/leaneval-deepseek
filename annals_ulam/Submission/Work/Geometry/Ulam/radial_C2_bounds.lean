import Mathlib
import Submission.Work.Geometry.Ulam.derivWithin_Icc_eq_deriv
import Submission.Work.Geometry.Ulam.derivWithin_derivWithin_Icc_eq_deriv_deriv
import Submission.Work.Geometry.Ulam.derivWithin_derivWithin_eq_deriv_deriv_of_pos

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped ContDiff Pointwise Interval Topology

set_option autoImplicit false

/-- The elementary lower bound from `C⁰`-closeness to `1`. -/
lemma radial_lower_bound_C2 {R : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (h : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |R α - 1| < η) :
    ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α := by
  intro α hα
  have hlt : |R α - 1| < η := h α hα
  have hle : -η < R α - 1 := (abs_lt.mp hlt).1
  linarith

/-- The mean-value upgrade: a `C¹` function with `f 0 = 0` and `|f'| ≤ η` on
`[0, π/2]` is bounded by `η * α`. -/
lemma radial_deriv_bound_C2 {R : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hR_diff : DifferentiableAt ℝ R 0)
    (hR_diff2 : DifferentiableAt ℝ (deriv R) 0)
    (hR_diff_end : DifferentiableAt ℝ R (Real.pi / 2))
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR0 : deriv R 0 = 0)
    (hR2 : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| < η) :
    ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α := by
  intro α hα
  let F : ℝ → ℝ := derivWithin R (Set.Icc 0 (Real.pi / 2))
  have hzero_pi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hU : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hzero_pi
  have hF_cont_all : ContinuousOn F (Set.Icc 0 (Real.pi / 2)) :=
    hR_cont.continuousOn_derivWithin hU (by simp)
  have hF_cont : ContinuousOn F (Set.Icc 0 α) := by
    refine hF_cont_all.mono ?_
    intro x hx
    exact ⟨hx.1, le_trans hx.2 hα.2⟩
  have hF_deriv : ∀ x ∈ Set.Ico 0 α,
      HasDerivWithinAt F (derivWithin F (Set.Icc 0 (Real.pi / 2)) x) (Set.Ici x) x := by
    intro x hx
    have hx_pos : 0 ≤ x := hx.1
    have hx_lt_alpha : x < α := hx.2
    have hx_lt_pi : x < Real.pi / 2 := lt_of_lt_of_le hx_lt_alpha hα.2
    have hx_mem : x ∈ Set.Icc 0 (Real.pi / 2) := ⟨hx_pos, le_of_lt hx_lt_pi⟩
    have hderiv_cont : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.Icc 0 (Real.pi / 2)) := by
      dsimp [F]
      exact hR_cont.derivWithin hU (by simp)
    have hF_cd : ContDiffWithinAt ℝ (⊤ : ℕ∞) F (Set.Icc 0 (Real.pi / 2)) x :=
      hderiv_cont.contDiffWithinAt hx_mem
    have hdiff : DifferentiableWithinAt ℝ F (Set.Icc 0 (Real.pi / 2)) x :=
      hF_cd.differentiableWithinAt (by simp)
    have hhas : HasDerivWithinAt F (derivWithin F (Set.Icc 0 (Real.pi / 2)) x)
        (Set.Icc 0 (Real.pi / 2)) x := hdiff.hasDerivWithinAt
    refine hhas.mono_of_mem_nhdsWithin ?_
    have hU_nhds : Set.Ioo (x - 1) (Real.pi / 2) ∈ 𝓝 x :=
      Ioo_mem_nhds (by linarith [hx_pos]) hx_lt_pi
    have hsub : Set.Ioo (x - 1) (Real.pi / 2) ∩ Set.Ici x ⊆ Set.Icc 0 (Real.pi / 2) := by
      intro y hy
      exact ⟨le_trans hx_pos hy.2, le_of_lt hy.1.2⟩
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [hU_nhds] with y hy hyIci
    exact hsub ⟨hy, hyIci⟩
  have hF_bound : ∀ x ∈ Set.Ico 0 α, ‖derivWithin F (Set.Icc 0 (Real.pi / 2)) x‖ ≤ η := by
    intro x hx
    have hx_mem : x ∈ Set.Icc 0 (Real.pi / 2) := ⟨hx.1, le_trans (le_of_lt hx.2) hα.2⟩
    have hx_lt_pi : x < Real.pi / 2 := lt_of_lt_of_le hx.2 hα.2
    have hident : derivWithin F (Set.Icc 0 (Real.pi / 2)) x = deriv (deriv R) x := by
      by_cases hx0 : x = 0
      · subst hx0
        dsimp [F]
        exact derivWithin_derivWithin_Icc_eq_deriv_deriv_of_differentiableAt hR_diff hR_diff2
      · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
        dsimp [F]
        exact derivWithin_derivWithin_eq_deriv_deriv_of_pos hx_pos hx_lt_pi
    rw [hident]
    have hlt := hR2 x hx_mem
    simpa [Real.norm_eq_abs] using le_of_lt hlt
  have hMVT := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := F) (f' := fun x => derivWithin F (Set.Icc 0 (Real.pi / 2)) x)
    (a := 0) (b := α) (C := η) hF_cont hF_deriv hF_bound α ⟨hα.1, le_rfl⟩
  have hF0 : F 0 = 0 := by
    dsimp [F]
    rw [derivWithin_Icc_eq_deriv_of_differentiableAt hR_diff, hR0]
  have hFα : F α = deriv R α := by
    dsimp [F]
    by_cases hα_eq : α = Real.pi / 2
    · subst hα_eq
      exact derivWithin_Icc_eq_deriv_at_pi_div_two_of_differentiableAt hR_diff_end
    · have hα_lt : α < Real.pi / 2 := lt_of_le_of_ne hα.2 hα_eq
      by_cases hα0 : α = 0
      · subst hα0
        exact derivWithin_Icc_eq_deriv_of_differentiableAt hR_diff
      · have hα_pos : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hα_pos hα_lt)
  have hnorm : |deriv R α| ≤ η * α := by
    have hMVT' : ‖F α - F 0‖ ≤ η * α := by simpa using hMVT
    rw [hF0, hFα] at hMVT'
    simpa [Real.norm_eq_abs, sub_zero] using hMVT'
  exact hnorm

end Commons.Geometry.Ulam

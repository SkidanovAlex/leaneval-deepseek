import Mathlib

namespace Work.FIArea7

open Filter
open scoped Topology

/-- A continuous function on `ℝ` that vanishes off `[0,1]` is bounded. -/
lemma exists_bound_of_continuous_eq_zero_off (g : ℝ → ℝ) (hg : Continuous g)
    (hzero : ∀ x : ℝ, x < 0 ∨ 1 < x → g x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |g x| ≤ C := by
  obtain ⟨x₀, -, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
      (hg.abs.continuousOn)
  refine ⟨|g x₀|, abs_nonneg _, fun x => ?_⟩
  rcases lt_or_ge x 0 with hx | hx
  · rw [hzero x (Or.inl hx), abs_zero]
    exact abs_nonneg _
  · rcases le_or_gt x 1 with hx1 | hx1
    · exact hmax ⟨hx, hx1⟩
    · rw [hzero x (Or.inr hx1), abs_zero]
      exact abs_nonneg _

theorem smoothTransition_deriv_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C) ∧
      (∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ C) := by
  have hcont1 : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).continuous_deriv_one
  have hcont2 : Continuous (deriv (deriv Real.smoothTransition)) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ (1 + 1) Real.smoothTransition).deriv').continuous_deriv_one
  have hz1 : ∀ x : ℝ, x < 0 ∨ 1 < x → deriv Real.smoothTransition x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      rw [h.deriv_eq, deriv_const]
    · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [h.deriv_eq, deriv_const]
  have hz2 : ∀ x : ℝ, x < 0 ∨ 1 < x → deriv (deriv Real.smoothTransition) x = 0 := by
    intro x hx
    have h : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      rcases hx with hx | hx
      · filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        exact hz1 y (Or.inl hy)
      · filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact hz1 y (Or.inr hy)
    rw [h.deriv_eq, deriv_const]
  obtain ⟨C1, hC1, hb1⟩ :=
    exists_bound_of_continuous_eq_zero_off (deriv Real.smoothTransition) hcont1 hz1
  obtain ⟨C2, hC2, hb2⟩ :=
    exists_bound_of_continuous_eq_zero_off (deriv (deriv Real.smoothTransition)) hcont2 hz2
  refine ⟨max C1 C2, le_trans hC1 (le_max_left _ _), fun x => ?_, fun x => ?_⟩
  · exact le_trans (hb1 x) (le_max_left _ _)
  · exact le_trans (hb2 x) (le_max_right _ _)

end Work.FIArea7

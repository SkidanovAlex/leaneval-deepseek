import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

/-- The average of a continuous real function over `[0,δ]` is at most its value at some point of
`[0,δ]`: a continuous function on the compact interval attains a maximum, and the integral of `F`
over `[0,δ]` is at most `δ` times that maximum.  (For `δ = 0` the interval is degenerate and the
statement is trivial.) -/
theorem integral_le_mul_of_continuousOn {F : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : ContinuousOn F (Set.Icc 0 δ)) :
    ∃ θ ∈ Set.Icc (0 : ℝ) δ, ∫ x in (0 : ℝ)..δ, F x ≤ δ * F θ := by
  obtain ⟨θ, hθ, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hδ⟩ hF
  refine ⟨θ, hθ, ?_⟩
  have h1 : ∫ x in (0 : ℝ)..δ, F x ≤ ∫ x in (0 : ℝ)..δ, F θ := by
    refine intervalIntegral.integral_mono_on hδ ?_ ?_ ?_
    · exact hF.intervalIntegrable_of_Icc hδ
    · exact continuous_const.intervalIntegrable _ _
    · intro x hx
      exact hmax hx
  rw [intervalIntegral.integral_const] at h1
  simpa using h1

end Work.BMF.HL

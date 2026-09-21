import Mathlib
import Submission.Work.OddRadon.RadialDefs

/-!
# The ball's radial graph is the semicircle

For the Euclidean ball the two radial functions are `ballR = ballr = 1`, so the upper and
lower boundary arcs are both `α ↦ (cos α, sin α)`.  The radial profile of this graph is the
semicircle `t ↦ √(1 - t²)`: indeed, for `α ∈ [0, π/2]` we have `sin α ≥ 0` and

  `√(1 - cos²α) = √(sin²α) = |sin α| = sin α`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- The semicircle profile evaluated at `cos α` is `sin α`, for `α ∈ [0, π/2]`. -/
theorem sqrt_one_sub_cos_sq {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.sqrt (1 - Real.cos α ^ 2) = Real.sin α := by
  have hsq : 1 - Real.cos α ^ 2 = Real.sin α ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hsin : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_mem_Icc ⟨hα.1, by linarith [Real.pi_pos, hα.2]⟩
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hsin]

theorem ball_profile_is_semicircle :
    IsRadialGraph ballR ballr (fun t : ℝ => Real.sqrt (1 - t ^ 2)) := by
  refine ⟨?_, ?_⟩
  · intro α hα
    show Real.sqrt (1 - (ballR α * Real.cos α) ^ 2) = ballR α * Real.sin α
    simpa [ballR] using sqrt_one_sub_cos_sq hα
  · intro α hα
    show Real.sqrt (1 - (-(ballr α * Real.cos α)) ^ 2) = ballr α * Real.sin α
    simpa [ballr] using sqrt_one_sub_cos_sq hα

end Work.OddRadon

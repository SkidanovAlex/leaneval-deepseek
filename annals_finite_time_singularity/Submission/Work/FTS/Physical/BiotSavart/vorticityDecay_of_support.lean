import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.BiotSavart

/-- **The `α`-power decay of a bounded vorticity of compact support.**

If `ω` vanishes outside the closed ball of radius `R` and `‖ω‖ ≤ M` everywhere, then
`‖ω x‖ ≤ C/(‖x‖^α + 1)` for all `x`, with the explicit constant `C = max 1 (M(R^α+1))`:
outside the ball the left-hand side vanishes, while inside it `‖x‖^α ≤ R^α`, so that
`M(‖x‖^α+1) ≤ M(R^α+1) ≤ C`. -/
theorem vorticityDecay_of_support {α : NNReal} {ω : Work.FTS.Physical.R3 → Work.FTS.Physical.R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hsupp : ∀ x : Work.FTS.Physical.R3, ω x ≠ 0 → x ∈ Metric.closedBall 0 R) (hbdd : ∀ x : Work.FTS.Physical.R3, ‖ω x‖ ≤ M) : ∃ C : ℝ, 0 < C ∧ ∀ x : Work.FTS.Physical.R3, ‖ω x‖ ≤ C / (‖x‖ ^ ((α : NNReal) : ℝ) + 1) := by
  refine ⟨max 1 (M * (R ^ (α : ℝ) + 1)), lt_of_lt_of_le one_pos (le_max_left _ _), fun x => ?_⟩
  rcases eq_or_ne (ω x) 0 with h0 | hne
  · rw [h0, norm_zero]
    positivity
  · -- the point lies in the support ball, so `‖x‖ ^ α ≤ R ^ α`
    have hxmem : x ∈ Metric.closedBall (0 : Work.FTS.Physical.R3) R := hsupp x hne
    rw [Metric.mem_closedBall, dist_zero_right] at hxmem
    have hxα : ‖x‖ ^ ((α : NNReal) : ℝ) ≤ R ^ (α : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg x) hxmem (by positivity)
    have hden : 0 < ‖x‖ ^ ((α : NNReal) : ℝ) + 1 := by
      have := Real.rpow_nonneg (norm_nonneg x) ((α : NNReal) : ℝ); linarith
    have hdenR : 0 < R ^ (α : ℝ) + 1 := by
      have := Real.rpow_nonneg hR (α : ℝ); linarith
    rw [le_div_iff₀ hden]
    have h1 : M * (R ^ (α : ℝ) + 1) ≤ max 1 (M * (R ^ (α : ℝ) + 1)) := le_max_right _ _
    have h2 : 1 ≤ max 1 (M * (R ^ (α : ℝ) + 1)) := le_max_left _ _
    nlinarith [hbdd x, h1, h2, hdenR, hxα, Real.rpow_nonneg (norm_nonneg x) ((α : NNReal) : ℝ)]

end Work.FTS.Physical.BiotSavart

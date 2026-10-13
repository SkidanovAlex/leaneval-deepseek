/-
# The `α`-power decay of the vorticity is preserved by the Euler scaling

The last datum clause that the scaling `u'(x,t) = λu(λx,λ²t)`, `u₀'(x) = λu₀(λx)` has to preserve is
the `α`-power decay of the vorticity
(`Work.SolutionDelivery.EulerScalingToUnitData` demands it of the produced datum `u₀'`):

  `‖∇×u₀' x‖ ≤ C / (‖x‖^α + 1)`  for some `C > 0`.

The vorticity scales as a single spatial derivative, `∇×(λ u₀(λ·)) x = λ² (∇×u₀)(λx)`
(`Submission.Work.SolutionDelivery.Scaling.vorticity_rescale`), and `‖λx‖ = |λ| ‖x‖`.  Writing
`r = ‖x‖` and `c = C`, the whole content is therefore the elementary real inequality

  `λ² (c / ((|λ| r)^α + 1)) ≤ (λ² c (|λ|^{-α} + 1)) / (r^α + 1)`,

whose new constant `λ² c (|λ|^{-α} + 1)` is positive for `λ ≠ 0`, `c > 0`
(`Submission.Work.SolutionDelivery.Scaling.rpow_scaling_bound`): the denominators satisfy
`r^α + 1 ≤ (|λ|^{-α} + 1)((|λ| r)^α + 1) = r^α + (|λ|^{-α} + |λ|^α r^α + 1)`.

Note `|λ|^{-α}` and not `λ^{-α}`: the decay is measured against `‖λx‖ = |λ|‖x‖`, and only
`|λ| ≠ 0` is used (all hypotheses are stated with `lam ≠ 0`, the sign of `λ` being irrelevant).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Scaling.Defs
import Submission.Work.SolutionDelivery.Scaling.vorticity_rescale
import Submission.Work.SolutionDelivery.Scaling.rpow_scaling_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery.Scaling

/-- **The `α`-power vorticity decay is preserved by the Euler scaling of the datum.**

If `‖∇×F x‖ ≤ C / (‖x‖^α + 1)` then, for the rescaled datum `rescaleDatum λ F = x ↦ λ • F (λ • x)`,
the vorticity `∇×(rescaleDatum λ F) x = λ² • (∇×F)(λx)` obeys the same decay with the constant
`λ² C (|λ|^{-α} + 1)`, which is positive because `λ ≠ 0` and `C > 0`. -/
theorem vorticityDecay_rescaleDatum {α : NNReal} {lam : ℝ} (hlam : lam ≠ 0)
    {F : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (h : Work.LWP.VorticityDecay α (FiniteTimeSingularity.vorticity F)) :
    Work.LWP.VorticityDecay α (FiniteTimeSingularity.vorticity
      (Work.SolutionDelivery.rescaleDatum lam F)) := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨lam ^ 2 * C * (|lam| ^ (-(α : ℝ)) + 1), ?_, fun x => ?_⟩
  · have h1 : 0 < lam ^ 2 := sq_pos_of_ne_zero hlam
    have h2 : 0 < |lam| ^ (-(α : ℝ)) + 1 := by
      have h3 := Real.rpow_pos_of_pos (abs_pos.mpr hlam) (-(α : ℝ))
      linarith
    exact mul_pos (mul_pos h1 hCpos) h2
  · -- the pointwise bound of `h` at the rescaled point, with `‖λ • x‖ = |λ| ‖x‖`
    have hb : ‖vorticity F (lam • x)‖ ≤ C / ((|lam| * ‖x‖) ^ (α : ℝ) + 1) := by
      simpa only [norm_smul, Real.norm_eq_abs] using hC (lam • x)
    rw [show Work.SolutionDelivery.rescaleDatum lam F
          = (fun y : Work.SolutionDelivery.R3 => lam • F (lam • y)) from rfl,
      vorticity_rescale hlam x, norm_smul, Real.norm_of_nonneg (sq_nonneg lam)]
    exact le_trans (mul_le_mul_of_nonneg_left hb (sq_nonneg lam))
      (rpow_scaling_bound hlam hCpos (norm_nonneg x))

end Work.SolutionDelivery.Scaling

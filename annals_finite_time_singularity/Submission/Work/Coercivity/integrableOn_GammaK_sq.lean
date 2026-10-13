import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Basic
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.CAux.integrableOn_GamK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- `Γ(θ)` is continuous on the angular interval `Iθ`: its base
`sin θ · cos²θ` is continuous and nonnegative there while `α/3 ≥ 0`. -/
theorem continuousOn_Gam (α : ℝ) (hα : 0 < α) :
    ContinuousOn (fun θ : ℝ => Spaces.Gam α θ) Spaces.Iθ := by
  have hα3 : (0 : ℝ) ≤ α / 3 := by linarith
  have hu : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Spaces.Iθ :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have h := hu.rpow_const (fun θ _ => Or.inr hα3)
  simpa [Spaces.Gam] using h

/-- `K(θ) = 3 sin θ cos²θ` is continuous on the angular interval `Iθ`. -/
theorem continuousOn_K :
    ContinuousOn (fun θ : ℝ => Spaces.K θ) Spaces.Iθ := by
  have h : Continuous (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) :=
    (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)
  simpa [Spaces.K] using h.continuousOn

/-- The angular function `Γ(θ)/c - K(θ)` is continuous on the compact interval `Iθ`,
hence its square is integrable there. -/
theorem integrableOn_GammaK_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) Spaces.Iθ := by
  have h : ContinuousOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) Spaces.Iθ :=
    (((continuousOn_Gam α hα).div_const _).sub continuousOn_K).pow 2
  simpa [Spaces.Iθ] using h.integrableOn_Icc

end Work.Coercivity

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces.CAux

open MeasureTheory Set

/-- On `[0,π/2]` the product `Γ(θ)K(θ) = (sin θ · cos²θ)^{α/3} · 3 sin θ cos²θ` is a
continuous function of `θ`, because the base `sin θ · cos²θ` is continuous and
nonnegative there while the exponent `α/3` is nonnegative.  It is therefore
integrable on the compact interval `Iθ`. -/
theorem integrableOn_GamK (α : ℝ) (hα : 0 < α) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
  have hα3 : (0 : ℝ) ≤ α / 3 := by linarith
  have hu : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Work.Spaces.Iθ :=
    hu.rpow_const (fun θ _ => Or.inr hα3)
  have hK : ContinuousOn (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
    ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
  have h2 : ContinuousOn
      (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (3 * Real.sin θ * Real.cos θ ^ 2))
      Work.Spaces.Iθ :=
    h1.mul hK
  have heq : (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (3 * Real.sin θ * Real.cos θ ^ 2) := by
    funext θ
    simp only [Work.Spaces.Gam, Work.Spaces.K]
  rw [heq]
  exact h2.integrableOn_Icc

end Work.Spaces.CAux

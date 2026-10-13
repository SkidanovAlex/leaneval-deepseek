import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The iterated integral defining `wip` agrees with the integral against the product
of the two restricted measures `(volume.restrict I_z) × (volume.restrict I_θ)`.

This is the Fubini bridge used to move between the two ways of writing the weighted
`L²` inner product `wip ρ g₁ g₂ = ∫∫ g₁ g₂ ρ`. -/
theorem wip_eq_integral_prod (ρ g₁ g₂ : ℝ → ℝ → ℝ)
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => g₁ z θ * g₂ z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip ρ g₁ g₂
      = ∫ p : ℝ × ℝ, g₁ p.1 p.2 * g₂ p.1 p.2 * ρ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the product of the two restricted measures is the restriction of the product measure
  have hvol : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => g₁ p.1 p.2 * g₂ p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← hvol]
    exact h
  rw [MeasureTheory.integral_prod
        (fun p : ℝ × ℝ => g₁ p.1 p.2 * g₂ p.1 p.2 * ρ p.1 p.2) hInt]
  rw [Work.Coercivity.wip]

end Work.Coercivity

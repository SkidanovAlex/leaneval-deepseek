import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.integrableOn_GammaK_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- The `(z,θ)`-separated integral of the projector correction with the sharp angular
bound.  The integrand factorises as `(1/(1+z)²) · (Γ(θ)/c)²`, and both factors are
integrable over the respective restricted measures:
`∫_z 1/(1+z)² = 1` (`integral_Iz_one_div_sq`) with `integrable_Iz_one_div_sq`, and
`(Γ/c)²` is integrable on `Iθ` since `Iθ` has finite measure and `|Γ/c| ≤ 10` pointwise
(`Gam_div_c_bound`).  Hence Fubini (`integral_prod_sep`, for the product of the restricted
measures, which is `volume.restrict (Iz ×ˢ Iθ)` by `volume_restrict_prod`) gives
`∫∫ (Γ(θ)/c)²/(1+z)² = (∫_z 1/(1+z)²)·(∫_θ (Γ/c)²) = ∫_θ (Γ/c)² ≤ 5`.

This is the sharp replacement for the *pointwise* bound `(Γ/c)² ≤ 100` used in
`ProjTransport_sq_integral_le` (`L2CoercivityTransport.lean`); it is the step that turns
the crude constant `2000` into `58` in the projector estimate. -/
theorem projCorr_sepIntegral_le_five (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hG : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 5) :
    ∫ p : ℝ × ℝ, (Spaces.Gam α p.2 / Spaces.c α) ^ 2 / (1 + p.1) ^ 2
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod
          (MeasureTheory.volume.restrict Spaces.Iθ)) ≤ 5 := by
  have haint : Integrable (fun z : ℝ => 1 / (1 + z) ^ 2)
      (MeasureTheory.volume.restrict Spaces.Iz) := integrable_Iz_one_div_sq
  have hbint : Integrable (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2)
      (MeasureTheory.volume.restrict Spaces.Iθ) := by
    have hcont : ContinuousOn (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2) Spaces.Iθ :=
      ((continuousOn_Gam α hα).div_const _).pow 2
    simpa only [Spaces.Iθ, IntegrableOn] using hcont.integrableOn_Icc
  have hcongr : (fun p : ℝ × ℝ =>
        (Spaces.Gam α p.2 / Spaces.c α) ^ 2 / (1 + p.1) ^ 2)
      = fun p : ℝ × ℝ =>
        (1 / (1 + p.1) ^ 2) * (Spaces.Gam α p.2 / Spaces.c α) ^ 2 := by
    funext p; ring
  rw [hcongr,
    integral_prod_sep (fun z : ℝ => 1 / (1 + z) ^ 2)
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2) haint hbint,
    integral_Iz_one_div_sq, one_mul]
  exact hG

end Work.Coercivity

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.H1IP_isHkIP
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityStep.Base

open MeasureTheory

/-- The `ℋ¹` inner product is symmetric, with no hypotheses on the profiles. -/
theorem H1IP_comm (α : ℝ) (f g : ℝ → ℝ → ℝ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α g f := by
  rw [Work.Coercivity.H1IP, Work.Coercivity.H1IP]
  rw [wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz f) (Work.Spaces.Dz g),
      wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f g,
      wip_comm (fun z _ => Work.Spaces.w z ^ 2) f g,
      wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth f) (Work.Spaces.Dth g)]


end Work.FTS.CoercivityStep.Base

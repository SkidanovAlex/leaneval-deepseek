import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

theorem integralSqSub {u v : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hv : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (huv : MeasureTheory.IntegrableOn
      (fun θ : ℝ => u θ * v θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ : ℝ => (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        - 2 * (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => u θ * v θ * Work.FTS.EllipticEst.thEta θ))
        + (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => (v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
  -- Expand `(u - v)² = u² - 2uv + v²` pointwise and use the linearity of the Bochner
  -- integral against the restricted measure `volume.restrict Iθ`; the three
  -- integrability hypotheses are exactly the ones the linearity rules need.
  set μ := MeasureTheory.volume.restrict Work.Spaces.Iθ
  have hgrp : (fun θ : ℝ => (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = fun θ : ℝ => ((u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          - 2 * (u θ * v θ * Work.FTS.EllipticEst.thEta θ))
          + (v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    funext θ; ring
  have h2w : MeasureTheory.Integrable
      (fun θ : ℝ => 2 * (u θ * v θ * Work.FTS.EllipticEst.thEta θ)) μ := huv.const_mul 2
  have hsub : MeasureTheory.Integrable
      (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        - 2 * (u θ * v θ * Work.FTS.EllipticEst.thEta θ)) μ := hu.sub h2w
  rw [hgrp, MeasureTheory.integral_add hsub hv,
      MeasureTheory.integral_sub hu h2w, MeasureTheory.integral_const_mul]

end Work.EllipticEst.Core.i0Aux.TVRed

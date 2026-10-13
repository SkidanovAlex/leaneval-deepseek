import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem EDz_eq_wip (f : ℝ → ℝ → ℝ) :
    EDz f = wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Spaces.Dz f) (Spaces.Dz f) := by
  simp only [EDz, Spaces.L2Sq, wip, wtEta, wtGam]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict (s := Spaces.Iθ) measurableSet_Icc] with θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · have := Real.pi_pos; linarith [hθ.2]
  have hr : (Real.sin (2 * θ) ^ (-(Spaces.eta / 2))) ^ 2 = Real.sin (2 * θ) ^ (-Spaces.eta) := by
    rw [← Real.rpow_natCast (Real.sin (2 * θ) ^ (-(Spaces.eta / 2))) 2]
    calc (Real.sin (2 * θ) ^ (-(Spaces.eta / 2))) ^ (2 : ℝ)
        = Real.sin (2 * θ) ^ ((-(Spaces.eta / 2)) * 2) :=
          (Real.rpow_mul hsin (-(Spaces.eta / 2)) (2 : ℝ)).symm
      _ = Real.sin (2 * θ) ^ (-Spaces.eta) := by
          rw [show (-(Spaces.eta / 2)) * 2 = -Spaces.eta by ring]
  rw [mul_pow, mul_pow, hr]
  ring

end Work.Coercivity

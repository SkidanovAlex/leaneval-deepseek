import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Set

/-- The function `a ↦ 1 + ‖a‖ ^ s` is integrable on any ball centred at the origin of `ℝ³`,
provided `s > -3` (which is exactly the threshold at which `‖a‖ ^ s` is integrable near the
origin in dimension `3`). -/
theorem integrableOn_one_add_norm_rpow_ball (s r : ℝ) (hs : -3 < s) :
    MeasureTheory.IntegrableOn (fun a : Work.LWP.R3 => 1 + (‖a‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) r) MeasureTheory.volume := by
  rcases le_or_gt r 0 with hr | hr
  · -- Empty ball.
    rw [Metric.ball_eq_empty.mpr hr]
    exact integrableOn_empty
  · -- Polar coordinates: integrability on the ball is equivalent to integrability on `(0, r)`
    -- of `y ↦ y ^ (3 - 1) * (1 + y ^ s) = y ^ 2 + y ^ (2 + s)`.
    rw [MeasureTheory.integrableOn_fun_norm_addHaar (μ := (volume : Measure Work.LWP.R3))
        (f := fun y : ℝ => 1 + y ^ s) (r := r)]
    have hdim : Module.finrank ℝ Work.LWP.R3 = 3 := by
      simp only [Work.LWP.R3]; exact finrank_euclideanSpace_fin
    rw [hdim]
    norm_num
    have h1 : IntegrableOn (fun y : ℝ => y ^ (2 : ℝ)) (Ioo 0 r) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by norm_num)
    have h2 : IntegrableOn (fun y : ℝ => y ^ (2 + s)) (Ioo 0 r) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by linarith)
    refine (h1.add h2).congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [Pi.add_apply]
    rw [Real.rpow_add hy.1, ← Real.rpow_natCast y 2]
    ring_nf

end Work.CoreResiduals.BiotSavart

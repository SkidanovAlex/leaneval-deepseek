import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.radial_rpow_integral
import Submission.Work.CoreResiduals.BiotSavart.integrableOn_one_add_norm_rpow_ball

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- `‖·‖ ^ s` is integrable on any ball of `ℝ³` when `s > -3`.  This is obtained from
`integrableOn_one_add_norm_rpow_ball` by subtracting the (integrable) constant `1`. -/
lemma integrableOn_norm_rpow_ball (s r : ℝ) (hs : -3 < s) :
    IntegrableOn (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) (Metric.ball (0 : Work.LWP.R3) r)
      volume := by
  classical
  have h1 : IntegrableOn (fun y : Work.LWP.R3 => 1 + (‖y‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) r) volume := integrableOn_one_add_norm_rpow_ball s r hs
  have h2 : IntegrableOn (fun _ : Work.LWP.R3 => (1 : ℝ)) (Metric.ball (0 : Work.LWP.R3) r)
      volume :=
    integrableOn_const (ne_of_lt (Metric.isBounded_ball).measure_lt_top) (by simp)
  have h3 : IntegrableOn (fun y : Work.LWP.R3 => (1 + (‖y‖ : ℝ) ^ s) - 1)
      (Metric.ball (0 : Work.LWP.R3) r) volume := h1.sub h2
  have h4 : (fun y : Work.LWP.R3 => (1 + (‖y‖ : ℝ) ^ s) - 1)
      = fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s := by
    funext y
    ring
  rwa [h4] at h3

/-- The `lintegral` form of the radial power integral over a ball of `ℝ³`:
`∫⁻_{‖y‖<R} ‖y‖^s = 4π R^{s+3}/(s+3)` for `s > -3`.  Since the integrand is non-negative
and integrable on the ball, the Lebesgue integral `∫⁻` of `ENNReal.ofReal` of it agrees with
`ENNReal.ofReal` of the Bochner integral `∫`, to which `radial_rpow_integral` applies. -/
theorem lintegral_ball_norm_rpow (s : ℝ) (hs : -3 < s) (R : ℝ) (hR : 0 < R) :
    ∫⁻ y in Metric.ball (0 : Work.LWP.R3) R, ENNReal.ofReal (‖y‖ ^ s)
      = ENNReal.ofReal (4 * Real.pi * R ^ (s + 3) / (s + 3)) := by
  have hint : IntegrableOn (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) R) volume := integrableOn_norm_rpow_ball s R hs
  have hInt : Integrable ((Metric.ball (0 : Work.LWP.R3) R).indicator
      (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hint
  have hnn : 0 ≤ᵐ[volume] (Metric.ball (0 : Work.LWP.R3) R).indicator
      (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) := by
    classical
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Set.indicator_apply, Pi.zero_apply]
    split_ifs with hy
    · exact Real.rpow_nonneg (norm_nonneg y) s
    · exact le_rfl
  have hcongr :
      ∫⁻ y, (Metric.ball (0 : Work.LWP.R3) R).indicator
          (fun y : Work.LWP.R3 => ENNReal.ofReal ((‖y‖ : ℝ) ^ s)) y
        = ∫⁻ y, ENNReal.ofReal ((Metric.ball (0 : Work.LWP.R3) R).indicator
            (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y) := by
    classical
    refine lintegral_congr (fun y => ?_)
    by_cases hy : y ∈ Metric.ball (0 : Work.LWP.R3) R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.ofReal_zero]
  have hofreal : ENNReal.ofReal (∫ y, (Metric.ball (0 : Work.LWP.R3) R).indicator
        (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y)
      = ∫⁻ y, ENNReal.ofReal ((Metric.ball (0 : Work.LWP.R3) R).indicator
        (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y) :=
    ofReal_integral_eq_lintegral_ofReal hInt hnn
  rw [← lintegral_indicator measurableSet_ball
    (fun y : Work.LWP.R3 => ENNReal.ofReal ((‖y‖ : ℝ) ^ s))]
  rw [hcongr, ← hofreal]
  rw [integral_indicator measurableSet_ball]
  rw [radial_rpow_integral s hs R hR]

end Work.CoreResiduals.BiotSavart

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.CoreResiduals.BiotSavart.polar_decomposition

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- The radial factor of the polar decomposition of the unit ball:
`∫_{(0,∞)} 1_{r < 1} r ^ 2 d(volumeIoiPow 2) = 1/5`, because `volumeIoiPow 2` has density
`r ↦ r ^ 2` on `(0,∞)`. -/
lemma volumeIoiPow_two_integral_indicator :
    ∫ r : Set.Ioi (0:ℝ), (if (r:ℝ) < 1 then (r:ℝ)^2 else 0) ∂(Measure.volumeIoiPow 2) = 1/5 := by
  rw [Measure.volumeIoiPow]
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun r : Set.Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^2))]
  · have htoReal : ∀ r : Set.Ioi (0:ℝ), (ENNReal.ofReal ((r:ℝ)^2)).toReal = (r:ℝ)^2 :=
      fun r => ENNReal.toReal_ofReal (sq_nonneg (r:ℝ))
    simp only [htoReal, smul_eq_mul]
    rw [integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioi
      (f := fun y : ℝ => y^2 * (if y < 1 then y^2 else 0))]
    have h1 : ∀ x ∈ Ioi (0:ℝ),
        x^2 * (if x < 1 then x^2 else 0) = (Iio (1:ℝ)).indicator (fun y => y^4) x := by
      intro x _
      by_cases hx1 : x < 1
      · rw [if_pos hx1, Set.indicator_of_mem (show x ∈ Iio (1:ℝ) from hx1)]
        ring
      · rw [if_neg hx1, mul_zero, Set.indicator_of_notMem (show x ∉ Iio (1:ℝ) from hx1)]
    rw [setIntegral_congr_fun measurableSet_Ioi h1]
    rw [setIntegral_indicator measurableSet_Iio]
    rw [show Ioi (0:ℝ) ∩ Iio (1:ℝ) = Ioo (0:ℝ) 1 from Ioi_inter_Iio]
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [integral_pow]
    norm_num
  · exact (measurable_subtype_coe.pow_const 2).ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

theorem sphere_ball_polar (h w : Work.LWP.R3) :
    (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
        (inner ℝ (u : Work.LWP.R3) h) * (inner ℝ (u : Work.LWP.R3) w)
        ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
      = 5 * ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
          (inner ℝ x h) * (inner ℝ x w) := by
  classical
  -- The polar-coordinate decomposition turns the unit-ball integral into the product of the
  -- sphere integral and the radial integral `∫_{(0,1)} r ^ 2 · r ^ 2 dr = 1/5`.
  have key : (∫ x in Metric.ball (0 : Work.LWP.R3) 1,
        (inner ℝ x h) * (inner ℝ x w))
      = (1/5) * (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
        (inner ℝ (u : Work.LWP.R3) h) * (inner ℝ (u : Work.LWP.R3) w)
        ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) := by
    rw [← integral_indicator measurableSet_ball]
    rw [polar_decomposition]
    have hcongr : ∀ p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ),
        (Metric.ball (0 : Work.LWP.R3) 1).indicator
          (fun x => (inner ℝ x h) * (inner ℝ x w)) (p.2.1 • (p.1.1 : Work.LWP.R3))
        = ((inner ℝ (p.1.1 : Work.LWP.R3) h) * (inner ℝ (p.1.1 : Work.LWP.R3) w))
          * (if (p.2.1 : ℝ) < 1 then (p.2.1 : ℝ)^2 else 0) := by
      intro p
      have hnorm : ‖(p.1.1 : Work.LWP.R3)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
      have hpos : (0:ℝ) < p.2.1 := p.2.2
      have hrsmul : ‖p.2.1 • (p.1.1 : Work.LWP.R3)‖ = p.2.1 := by
        rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
      have hmem : (p.2.1 • (p.1.1 : Work.LWP.R3)) ∈ Metric.ball (0 : Work.LWP.R3) 1
          ↔ p.2.1 < 1 := by
        rw [Metric.mem_ball, dist_zero_right, hrsmul]
      rw [Set.indicator_apply]
      by_cases hlt : (p.2.1 : ℝ) < 1
      · rw [if_pos (hmem.mpr hlt), if_pos hlt, real_inner_smul_left, real_inner_smul_left]
        ring
      · rw [if_neg (fun hh => hlt (hmem.mp hh)), if_neg hlt, mul_zero]
    simp_rw [hcongr]
    rw [integral_prod_mul
      (f := fun u : Metric.sphere (0 : Work.LWP.R3) 1 =>
        (inner ℝ (u : Work.LWP.R3) h) * (inner ℝ (u : Work.LWP.R3) w))
      (g := fun r : Set.Ioi (0:ℝ) => if (r:ℝ) < 1 then (r:ℝ)^2 else 0)]
    rw [volumeIoiPow_two_integral_indicator]
    ring
  rw [key]
  ring

end Work.CoreResiduals.BiotSavart

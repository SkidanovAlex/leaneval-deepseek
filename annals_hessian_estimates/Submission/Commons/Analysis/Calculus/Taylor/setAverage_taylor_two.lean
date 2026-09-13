import Mathlib
import Submission.Commons.Analysis.Calculus.Taylor.taylor_two_remainder_integral
import Submission.Commons.Analysis.Measure.setAverage_ball_add
import Submission.Commons.Analysis.Measure.setAverage_mul_const
import Submission.Commons.Measure.Lebesgue.setAverage_comp_smul_ball

namespace Commons.Analysis.Calculus.Taylor

open MeasureTheory Metric Set Filter Function
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution
open Commons.Analysis.Measure Commons.Measure.Lebesgue

/-- **Fubini** between a set average and an interval integral: if the (uncurried) integrand is
integrable on the product of the averaging set with `Ioc 0 1`, then the average of the inner
interval integral equals the interval integral of the inner averages. -/
theorem setAverage_intervalIntegral_swap {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    (h : Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ => f p.1 * g p.1 p.2)
      ((volume.restrict s).prod (volume.restrict (Set.Ioc 0 1)))) :
    (⨍ w in s, f w * (∫ t in (0:ℝ)..1, g w t))
      = ∫ t in (0:ℝ)..1, ⨍ w in s, f w * g w t := by
  have hX : (∫ w in s, f w * (∫ t in (0:ℝ)..1, g w t))
      = ∫ t in (0:ℝ)..1, ∫ w in s, f w * g w t := by
    rw [show (∫ w in s, f w * (∫ t in (0:ℝ)..1, g w t))
          = ∫ w in s, ∫ t in (0:ℝ)..1, f w * g w t from
        integral_congr_ae (Filter.Eventually.of_forall fun w =>
          (intervalIntegral.integral_const_mul (f w) (fun t => g w t)).symm)]
    rw [intervalIntegral_integral_swap (μ := volume.restrict s) (f := fun t w => f w * g w t)
      (by rw [Set.uIoc_of_le zero_le_one]; exact h.swap)]
  have hR : (∫ t in (0:ℝ)..1, ⨍ w in s, f w * g w t)
      = (volume.real s)⁻¹ * ∫ t in (0:ℝ)..1, ∫ w in s, f w * g w t := by
    rw [show (∫ t in (0:ℝ)..1, ⨍ w in s, f w * g w t)
          = ∫ t in (0:ℝ)..1, (volume.real s)⁻¹ * ∫ w in s, f w * g w t from by
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [setAverage_eq, smul_eq_mul]]
    rw [intervalIntegral.integral_const_mul]
  rw [setAverage_eq, hX, hR, smul_eq_mul]

/-- **Change of variables** `z = t • w` in the average over a ball, for the specific integrand
`ψ (x₀ + t⁻¹ • z) * ((D²U (x₀ + z) - M₀) z z)`: dilating the ball by the factor `t` rescales the
quadratic integrand by `t ^ 2`. -/
theorem setAverage_ball_comp_smul_second_deriv {n : ℕ} {U : EuclideanSpace ℝ (Fin n) → ℝ}
    {M₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {r t : ℝ}
    (ht : 0 < t) (hr : 0 < r) :
    (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r),
        ψ (x₀ + t⁻¹ • z) * ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z))
      = t ^ 2 * ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w) := by
  have hpt : ∀ w : EuclideanSpace ℝ (Fin n),
      ψ (x₀ + t⁻¹ • (t • w)) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) (t • w) (t • w))
        = t ^ 2 * (ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)) := by
    intro w
    have htw : t⁻¹ • (t • w) = w := by rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    rw [htw]
    have hA : ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) (t • w)) (t • w)
        = t ^ 2 * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w) := by
      simp only [map_smul, smul_apply, smul_eq_mul, pow_two]
      ring
    rw [hA]
    ring
  calc (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r),
        ψ (x₀ + t⁻¹ • z) * ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z))
      = ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          (fun z => ψ (x₀ + t⁻¹ • z) * ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)) (t • w) :=
        (setAverage_comp_smul_ball
          (f := fun z => ψ (x₀ + t⁻¹ • z) * ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z))
          ht hr).symm
    _ = ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          t ^ 2 * (ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)) :=
        setAverage_congr_fun measurableSet_ball (Filter.Eventually.of_forall (fun w _ => hpt w))
    _ = t ^ 2 * ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w) := by
        rw [setAverage_mul_const]

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem setAverage_taylor_two {n : ℕ} {U : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {M₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {r : ℝ} (hr : 0 < r)
    (hU : ContDiff ℝ 2 U) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (⨍ y in Metric.ball x₀ r,
        ψ y * (U y - U x₀ - (fderiv ℝ U x₀) (y - x₀) - (1/2 : ℝ) * M₀ (y - x₀) (y - x₀)))
      = ∫ t in (0:ℝ)..1, (1 - t) / t ^ 2 *
          (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r),
            ψ (x₀ + t⁻¹ • z) *
              ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)) := by
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
      U y - U x₀ - (fderiv ℝ U x₀) (y - x₀) - (1/2 : ℝ) * M₀ (y - x₀) (y - x₀)
        = ∫ t in (0:ℝ)..1,
            (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • (y - x₀)) - M₀) (y - x₀) (y - x₀)) := by
    intro y
    have h := taylor_two_remainder_integral (x₀ := x₀) (M₀ := M₀) hU (y - x₀)
    rw [show x₀ + (y - x₀) = y from by abel] at h
    exact h
  have h1 : (⨍ y in Metric.ball x₀ r,
        ψ y * (U y - U x₀ - (fderiv ℝ U x₀) (y - x₀) - (1/2 : ℝ) * M₀ (y - x₀) (y - x₀)))
      = ⨍ y in Metric.ball x₀ r,
          ψ y * (∫ t in (0:ℝ)..1,
            (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • (y - x₀)) - M₀) (y - x₀) (y - x₀))) := by
    apply setAverage_congr_fun measurableSet_ball
    filter_upwards with y hy
    rw [hpt y]
  have h2 : (⨍ y in Metric.ball x₀ r,
          ψ y * (∫ t in (0:ℝ)..1,
            (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • (y - x₀)) - M₀) (y - x₀) (y - x₀))))
      = ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * (∫ t in (0:ℝ)..1,
            (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)) := by
    rw [setAverage_ball_add]
    apply setAverage_congr_fun measurableSet_ball
    filter_upwards with w hw
    show ψ (x₀ + w) * (∫ t in (0:ℝ)..1,
          (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • ((x₀ + w) - x₀)) - M₀) ((x₀ + w) - x₀) ((x₀ + w) - x₀)))
        = ψ (x₀ + w) * (∫ t in (0:ℝ)..1,
          (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w))
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [add_sub_cancel_left]
  have hInt : Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        ψ (x₀ + p.1) * ((1 - p.2) * ((fderiv ℝ (fderiv ℝ U) (x₀ + p.2 • p.1) - M₀) p.1 p.1)))
      ((volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).prod
        (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        ψ (x₀ + p.1) * ((1 - p.2) * ((fderiv ℝ (fderiv ℝ U) (x₀ + p.2 • p.1) - M₀) p.1 p.1))) := by
      fun_prop
    rw [Measure.prod_restrict]
    exact IntegrableOn.mono_set
      (ContinuousOn.integrableOn_compact ((isCompact_closedBall 0 r).prod isCompact_Icc)
        hcont.continuousOn)
      (Set.prod_mono Metric.ball_subset_closedBall Set.Ioc_subset_Icc_self)
  have h3 : (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * (∫ t in (0:ℝ)..1,
            (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)))
      = ∫ t in (0:ℝ)..1, ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)) :=
    setAverage_intervalIntegral_swap (f := fun w => ψ (x₀ + w))
      (g := fun w t => (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)) hInt
  have h4 : (∫ t in (0:ℝ)..1, ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)))
      = ∫ t in (0:ℝ)..1, (1 - t) * ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)))
        = (1 - t) * (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w))
    rw [show (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w)))
        = (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          (1 - t) * (ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w))) from
      setAverage_congr_fun measurableSet_ball
        (Filter.Eventually.of_forall (fun w _ => by ring))]
    rw [setAverage_mul_const]
  have h5 : (∫ t in (0:ℝ)..1, (1 - t) * ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w))
      = ∫ t in (0:ℝ)..1, (1 - t) / t ^ 2 *
          (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r),
            ψ (x₀ + t⁻¹ • z) *
              ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have htpos : 0 < t := ht.1
    show (1 - t) * (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ψ (x₀ + w) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • w) - M₀) w w))
        = (1 - t) / t ^ 2 *
          (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r),
            ψ (x₀ + t⁻¹ • z) * ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z))
    rw [setAverage_ball_comp_smul_second_deriv (ht := htpos) (hr := hr)]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 htpos.ne'
    field_simp
  rw [h1, h2, h3, h4, h5]

end Commons.Analysis.Calculus.Taylor

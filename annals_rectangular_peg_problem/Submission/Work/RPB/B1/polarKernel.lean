import Mathlib
import Submission.Work.RPB.B1.PolarDefs
import Submission.Work.RPB.B1.polar_region
import Submission.Work.RPB.B1.polar_pointwise
import Submission.Work.RPB.B1.radial_periodic
import Submission.Work.RPB.B1.polarIntegrand_slice
import Submission.Work.RPB.B1.polarIntegrand_integrable

/-!
# `Work.RPB.B1.polarKernel`

The rectangular-peg "polar kernel" identity: for `‖a‖ < R`,

`∫ q in ball 0 R, (C / (a - q)).im
   = ∫ θ in 0..2π, (C e^{-iθ}).im · (Re (a e^{-iθ}) + √(R² - Im (a e^{-iθ})²))`.

Geometrically the right hand side is the polar parametrisation of the disc `ball 0 R` centred at
the pole `a`: writing `a - q = ρ e^{iφ}`, the radial extent of the translated disc `ball a R` in
direction `φ` is `radial a R φ = Re (a e^{-iφ}) + √(R² - Im (a e^{-iφ})²)`, and after the polar
change of variables the Jacobian factor `ρ` cancels the `1/ρ` in the integrand, leaving the pure
angular kernel `(C e^{-iφ}).im`.

The proof is assembled from the following pieces:
* `polarKernel_sub_ball`: translation/reflection invariance of the disc integral (moving the pole
  to the origin of the disc);
* `Complex.integral_comp_polarCoord_symm` (Mathlib): the polar change of variables;
* `polarKernel_reduce`: the pointwise reduction of the polar integrand, using `polar_region`
  (membership of the disc in polar coordinates) and `polar_pointwise` (cancellation of the radial
  factor);
* `polarKernel_fubini`: Tonelli/Fubini together with the explicit radial slice
  (`polarIntegrand_slice`, `polarIntegrand_integrable`);
* `radial_periodic`: the shift of the angular integral from `(-π, π)` to `(0, 2π)`.
-/

namespace Work.RPB.B1

open MeasureTheory Set Complex Real
open scoped Real

noncomputable section

/-- Translation/reflection invariance of the integral around a disc: the change of variables
`q ↦ a - q` (an isometry of `ℂ`) maps `ball 0 R` onto `ball a R`. -/
theorem polarKernel_sub_ball (a : ℂ) {R : ℝ} (F : ℂ → ℝ) :
    ∫ q in Metric.ball (0 : ℂ) R, F (a - q) = ∫ z in Metric.ball a R, F z := by
  classical
  have hb0 : MeasurableSet (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball.measurableSet
  have hba : MeasurableSet (Metric.ball a R) := Metric.isOpen_ball.measurableSet
  set G : ℂ → ℝ := (Metric.ball a R).indicator F with hG
  have hkey : ∀ q : ℂ, (q ∈ Metric.ball (0 : ℂ) R) ↔ (a - q ∈ Metric.ball a R) := by
    intro q
    simp only [Metric.mem_ball, dist_eq_norm]
    rw [show (a - q) - a = -q by ring, norm_neg, sub_zero]
  have h1 : (∫ q in Metric.ball (0 : ℂ) R, F (a - q)) = ∫ q, G (a - q) := by
    rw [← MeasureTheory.integral_indicator hb0 (f := fun q => F (a - q))]
    apply integral_congr_ae
    filter_upwards with q
    rw [hG, Set.indicator_apply, Set.indicator_apply, hkey q]
  have h2 : (∫ q, G (a - q)) = ∫ q, G (a + q) :=
    MeasureTheory.integral_neg_eq_self (fun q => G (a + q)) volume
  have h3 : (∫ q, G (a + q)) = ∫ z, G z :=
    MeasureTheory.integral_add_left_eq_self G a
  have h4 : (∫ z, G z) = ∫ z in Metric.ball a R, F z := by
    rw [hG]
    exact MeasureTheory.integral_indicator hba
  rw [h1, h2, h3, h4]

/-- The polar change of variables, stated with the disc integral on the left: the integral over
`ball a R` equals the integral over the polar target of the Jacobian-weighted integrand. -/
theorem polarKernel_polar (a C : ℂ) {R : ℝ} :
    (∫ z in Metric.ball a R, (C / z).im)
      = ∫ p in polarTarget,
          p.1 • (Metric.ball a R).indicator (fun z => (C / z).im) (Complex.polarCoord.symm p) := by
  rw [polarTarget]
  rw [← MeasureTheory.integral_indicator Metric.isOpen_ball.measurableSet
    (f := fun z => (C / z).im)]
  exact (Complex.integral_comp_polarCoord_symm
    (fun z => (Metric.ball a R).indicator (fun z => (C / z).im) z)).symm

/-- Pointwise reduction of the polar integrand to `polarIntegrand`. -/
theorem polarKernel_reduce (a C : ℂ) {R : ℝ} (hR : ‖a‖ < R) :
    (∫ p in polarTarget,
        p.1 • (Metric.ball a R).indicator (fun z => (C / z).im) (Complex.polarCoord.symm p))
      = ∫ p in polarTarget, polarIntegrand a C R p := by
  classical
  refine setIntegral_congr_fun measurableSet_polarTarget (fun p hp => ?_)
  have hp1 : 0 < p.1 := hp.1
  have hiff : Complex.polarCoord.symm p ∈ Metric.ball a R ↔ p.1 < radial a R p.2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact polar_region a hR p.1 p.2 hp1
  rw [polarIntegrand, smul_eq_mul, Set.indicator_apply]
  by_cases h : Complex.polarCoord.symm p ∈ Metric.ball a R
  · rw [if_pos h, if_pos (hiff.mp h)]
    exact polar_pointwise C p hp1.ne'
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
    ring

/-- Tonelli/Fubini reduction of the polar integral to the angular integral of `radial`. -/
theorem polarKernel_fubini (a C : ℂ) {R : ℝ} (hR : ‖a‖ < R) :
    (∫ p in polarTarget, polarIntegrand a C R p)
      = ∫ θ in (-Real.pi)..Real.pi,
          (C * Complex.exp (-(θ : ℂ) * Complex.I)).im * radial a R θ := by
  rw [← MeasureTheory.integral_indicator measurableSet_polarTarget
    (f := polarIntegrand a C R)]
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := rfl
  rw [hvol]
  rw [MeasureTheory.integral_prod_symm _ (polarIntegrand_integrable a C hR)]
  have hcongr : (∫ φ, ∫ r, (polarTarget.indicator (polarIntegrand a C R)) (r, φ))
      = ∫ φ, (Set.Ioo (-Real.pi) Real.pi).indicator
          (fun φ => (C * Complex.exp (-(φ : ℂ) * Complex.I)).im * radial a R φ) φ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with φ
    exact polarIntegrand_slice a C hR φ
  rw [hcongr]
  rw [MeasureTheory.integral_indicator measurableSet_Ioo]
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioo_ae_eq_Ioc (a := -Real.pi) (b := Real.pi))]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- **The rectangular-peg polar kernel identity.** -/
theorem polarKernel (a C : ℂ) {R : ℝ} (hR : ‖a‖ < R) :
    ∫ q in Metric.ball (0 : ℂ) R, (C / (a - q)).im
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (C * Complex.exp (-(θ : ℂ) * Complex.I)).im *
            ((a * Complex.exp (-(θ : ℂ) * Complex.I)).re +
              Real.sqrt (R ^ 2 - (a * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2)) := by
  have hmain : (∫ q in Metric.ball (0 : ℂ) R, (C / (a - q)).im)
      = ∫ θ in (-Real.pi)..Real.pi,
          (C * Complex.exp (-(θ : ℂ) * Complex.I)).im * radial a R θ := by
    rw [polarKernel_sub_ball a (fun z => (C / z).im)]
    rw [polarKernel_polar a C]
    rw [polarKernel_reduce a C hR]
    rw [polarKernel_fubini a C hR]
  rw [hmain]
  have hshift : (∫ θ in (-Real.pi)..Real.pi,
        (C * Complex.exp (-(θ : ℂ) * Complex.I)).im * radial a R θ)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (C * Complex.exp (-(θ : ℂ) * Complex.I)).im * radial a R θ := by
    have h := (radial_periodic a C R).intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h
    exact h
  rw [hshift]
  simp only [radial]

end

end Work.RPB.B1

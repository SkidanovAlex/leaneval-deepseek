import Mathlib
import Submission.Work.Smooth.Jordan.Circle

/-!
# The winding number of the unit circle around an interior point

For a point `x` in the open unit disc, the standard circle `t ↦ e^{it}` winds once around `x`,
so `wind unitCircle x = 1`.

The proof identifies the winding integral with the circle integral of `z ↦ (z - x)⁻¹` over the
unit circle (`circleMap 0 1` is exactly `unitCircle.γ`), and evaluates it with the Cauchy formula
`circleIntegral.integral_sub_inv_of_mem_ball`.
-/

open Set
open Classical

namespace Work.Smooth.Jordan

noncomputable section

/-- The derivative of the standard circle. -/
theorem deriv_unitCircle (t : ℝ) :
    deriv unitCircle.γ t = Complex.exp ((t : ℂ) * Complex.I) * Complex.I := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ) * Complex.I)) Complex.I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
    simpa using h1.cexp
  exact h2.deriv

/-- The standard circle is the circle map of centre `0` and radius `1`. -/
@[simp] theorem circleMap_zero_one_apply (t : ℝ) :
    circleMap (0 : ℂ) 1 t = unitCircle.γ t := by
  simp [circleMap, unitCircle_apply]

/-- The winding integral of the standard circle around `x` is the circle integral of
`z ↦ (z - x)⁻¹`. -/
theorem windingPrimitive_unitCircle (x : ℂ) :
    (∫ s in (0 : ℝ)..(2 * Real.pi), windingIntegrand unitCircle x s)
      = ∮ z in C((0 : ℂ), 1), (z - x)⁻¹ := by
  have hderiv : ∀ t : ℝ, deriv unitCircle.γ t = circleMap (0 : ℂ) 1 t * Complex.I := by
    intro t
    rw [deriv_unitCircle t, circleMap]
    simp
  rw [circleIntegral]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [windingIntegrand_apply]
  rw [hderiv t, deriv_circleMap, circleMap]
  simp [smul_eq_mul, div_eq_mul_inv]

/-- **The unit circle winds once around every point of the open unit disc.** -/
theorem unitCircle_wind_inside (x : ℂ) (hx : ‖x‖ < 1) : wind unitCircle x = 1 := by
  rw [wind_def, windingPrimitive, windingPrimitive_unitCircle]
  rw [circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := x) (R := 1) (by
    simpa [Metric.mem_ball, dist_eq_norm] using hx)]
  rw [inv_mul_cancel₀ two_pi_I_ne_zero]

end

end Work.Smooth.Jordan

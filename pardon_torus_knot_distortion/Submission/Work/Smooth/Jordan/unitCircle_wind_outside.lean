import Mathlib
import Submission.Work.Smooth.Jordan.Circle

/-!
# The unit circle winds zero times around every exterior point

For a point `x` of the plane with `‖x‖ > 1`, the standard circle `t ↦ e^{it}` does not wind
around `x`, so the winding integral `wind unitCircle x` vanishes.

The proof is the explicit primitive of the winding integrand.  Since `‖x‖ > 1`, the curve
`t ↦ 1 - e^{it}/x` takes its values in the open right half-plane, hence in the slit plane
`Complex.slitPlane = {z | 0 < z.re ∨ z.im ≠ 0}`, where `Complex.log` is holomorphic with
derivative `z⁻¹`.  Therefore

`F t = log (1 - e^{it}/x)`,   `F' t = (-e^{it}·i/x) / (1 - e^{it}/x) = i·e^{it}/(e^{it} - x)`,

which is exactly the winding integrand `γ'(t)/(γ(t) - x)` of the standard circle.  Since
`e^{2πi} = 1`, the primitive is `2π`-periodic, `F (2π) = F 0`, so the total integral over one
period is zero.
-/

open Set
open MeasureTheory

namespace Work.Smooth.Jordan

noncomputable section

/-- The derivative of the standard unit circle `t ↦ e^{it}`. -/
private theorem deriv_unitCircle_aux (t : ℝ) :
    deriv unitCircle.γ t = Complex.I * Complex.exp ((t : ℂ) * Complex.I) := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
    have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (Complex.ofRealCLM.hasDerivAt (x := t))
    simpa using h.mul_const Complex.I
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := h1.cexp
  have h3 := h2.deriv
  rw [mul_comm] at h3
  exact h3

/-- For `‖x‖ > 1` the function `t ↦ log (1 - e^{it}/x)` is a primitive of the winding integrand
of the standard circle around `x`. -/
private theorem hasDerivAt_unitCircle_logPrimitive (x : ℂ) (hx : 1 < ‖x‖) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.log (1 - Complex.exp ((s : ℂ) * Complex.I) / x))
      (windingIntegrand unitCircle x t) t := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hx; simp at hx; linarith
  -- `1 - e^{it}/x` lies in the slit plane, indeed in the open right half-plane
  have hslit : (1 - Complex.exp ((t : ℂ) * Complex.I) / x) ∈ Complex.slitPlane := by
    have hxpos : (0 : ℝ) < ‖x‖ := by linarith
    have hlt : ‖Complex.exp ((t : ℂ) * Complex.I) / x‖ < 1 := by
      rw [norm_div, Complex.norm_exp_ofReal_mul_I, div_lt_one hxpos]
      exact hx
    rw [Complex.slitPlane]
    show (0 : ℝ) < (1 - Complex.exp ((t : ℂ) * Complex.I) / x).re ∨ _
    left
    rw [Complex.sub_re, Complex.one_re]
    have := Complex.re_le_norm (Complex.exp ((t : ℂ) * Complex.I) / x)
    linarith
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
    have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (Complex.ofRealCLM.hasDerivAt (x := t))
    simpa using h.mul_const Complex.I
  have hq : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I) / x)
      (Complex.exp ((t : ℂ) * Complex.I) * Complex.I / x) t := h1.cexp.div_const x
  have hu : HasDerivAt (fun s : ℝ => 1 - Complex.exp ((s : ℂ) * Complex.I) / x)
      (0 - Complex.exp ((t : ℂ) * Complex.I) * Complex.I / x) t :=
    (hasDerivAt_const (x := t) (1 : ℂ)).sub hq
  have hlog := hu.clog_real hslit
  -- rewrite the winding integrand into the shape produced by `HasDerivAt.clog_real`
  rw [windingIntegrand_apply, unitCircle_apply, deriv_unitCircle_aux]
  convert hlog using 1
  rw [show Complex.exp ((t : ℂ) * Complex.I) - x = -(x - Complex.exp ((t : ℂ) * Complex.I)) by
    ring, div_neg]
  field_simp
  ring

/-- **The standard unit circle winds zero times around every point outside the closed unit
disc.** -/
theorem unitCircle_wind_outside (x : ℂ) (hx : 1 < ‖x‖) : wind unitCircle x = 0 := by
  -- `x` is off the trace, so the integrand is continuous
  have hxtrace : x ∉ unitCircle.trace := by
    intro hmem
    rw [unitCircle_trace, Metric.mem_sphere, dist_zero_right] at hmem
    linarith
  have hInt : windingPrimitive unitCircle x (2 * Real.pi) = 0 := by
    have hcont : IntervalIntegrable (windingIntegrand unitCircle x) volume (0 : ℝ) (2 * Real.pi) :=
      (continuous_windingIntegrand unitCircle hxtrace).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => Complex.log (1 - Complex.exp ((s : ℂ) * Complex.I) / x))
      (f' := windingIntegrand unitCircle x)
      (fun t _ => hasDerivAt_unitCircle_logPrimitive x hx t) hcont
    show (∫ s in (0 : ℝ)..(2 * Real.pi), windingIntegrand unitCircle x s) = 0
    rw [h]
    show Complex.log (1 - Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) / x)
        - Complex.log (1 - Complex.exp (((0 : ℝ) : ℂ) * Complex.I) / x) = 0
    have h2 : Complex.log (1 - Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) / x)
        = Complex.log (1 - 1 / x) := by
      have harg : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_two_pi_mul_I]
    have h0 : Complex.log (1 - Complex.exp (((0 : ℝ) : ℂ) * Complex.I) / x)
        = Complex.log (1 - 1 / x) := by simp
    rw [h2, h0, sub_self]
  rw [wind_def, hInt, mul_zero]

end

end Work.Smooth.Jordan

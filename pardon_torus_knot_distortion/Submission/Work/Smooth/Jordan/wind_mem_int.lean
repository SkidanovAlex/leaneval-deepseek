import Mathlib
import Submission.Work.Smooth.Jordan.Index

/-!
# Integrality of the winding integral

For a `C¹` closed plane curve `c` and a point `x` off its trace, the winding integral

`wind c x = (2πi)⁻¹ ∮ dz/(z - x) = (2πi)⁻¹ ∫₀^{2π} γ'(t)/(γ(t) - x) dt`

is an integer.  This file proves that fact by exponentiating the primitive:

* `windingPrimitive_hasDerivAt` — the primitive `t ↦ ∫₀^t γ'/(γ - x)` differentiates back to the
  integrand;
* `windingPrimitive_const_exp` — consequently `t ↦ (γ t - x) · exp(-(primitive t))` is constant,
  so `exp(-(primitive 2π)) = 1` because `γ` is `2π`-periodic;
* `windingPrimitive_int` — hence the primitive at `2π` is an integral multiple of `2πi`;
* `wind_mem_int` — and `wind c x` is that integer.
-/

open Set MeasureTheory
open scoped Topology

namespace Work.Smooth.Jordan

noncomputable section

/-- **The primitive of the winding integrand differentiates back to the integrand.**  This is the
fundamental theorem of calculus applied to the (continuous, off the trace) integrand. -/
theorem windingPrimitive_hasDerivAt (c : SmoothPlaneCurve) {x : ℂ} (hx : x ∉ c.trace) (t : ℝ) :
    HasDerivAt (windingPrimitive c x) (windingIntegrand c x t) t := by
  have hcont : Continuous (windingIntegrand c x) := continuous_windingIntegrand c hx
  have h := intervalIntegral.integral_hasDerivAt_right (f := windingIntegrand c x) (a := 0) (b := t)
    (hcont.intervalIntegrable 0 t) (hcont.stronglyMeasurableAtFilter volume (𝓝 t))
    hcont.continuousAt
  exact h

/-- **The exponential factor is constant.**  Since the integrand is `γ'/(γ - x)`, the derivative of
`t ↦ (γ t - x) · exp(-(P t))`, where `P` is the primitive of the integrand, vanishes identically;
hence the function is constant, equal to its value `γ 0 - x` at `0`. -/
theorem windingPrimitive_const_exp (c : SmoothPlaneCurve) {x : ℂ} (hx : x ∉ c.trace) (t : ℝ) :
    (c.γ t - x) * Complex.exp (-(windingPrimitive c x t)) = c.γ 0 - x := by
  have hne : ∀ s : ℝ, c.γ s - x ≠ 0 := by
    intro s h
    exact hx (sub_eq_zero.mp h ▸ c.mem_trace s)
  have hcont : Continuous (windingIntegrand c x) := continuous_windingIntegrand c hx
  have hp : ∀ s : ℝ, HasDerivAt (windingPrimitive c x) (windingIntegrand c x s) s :=
    windingPrimitive_hasDerivAt c hx
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => (c.γ u - x) * Complex.exp (-(windingPrimitive c x u))) 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => c.γ u - x) (deriv c.γ s) s :=
      (c.differentiable s).hasDerivAt.sub_const x
    have h3 := (hp s).neg.cexp
    have h4 : HasDerivAt (fun u : ℝ => (c.γ u - x) * Complex.exp (-(windingPrimitive c x u)))
        (deriv c.γ s * Complex.exp (-(windingPrimitive c x s))
          + (c.γ s - x)
            * (Complex.exp (-(windingPrimitive c x s)) * (-(windingIntegrand c x s)))) s :=
      h1.mul h3
    have hmul : (c.γ s - x) * (deriv c.γ s / (c.γ s - x)) = deriv c.γ s :=
      mul_div_cancel₀ (deriv c.γ s) (hne s)
    have hzero : deriv c.γ s * Complex.exp (-(windingPrimitive c x s))
        + (c.γ s - x)
          * (Complex.exp (-(windingPrimitive c x s)) * (-(windingIntegrand c x s))) = 0 := by
      rw [windingIntegrand_apply]
      have key : (c.γ s - x)
            * (Complex.exp (-(windingPrimitive c x s)) * (-(deriv c.γ s / (c.γ s - x))))
          = -(deriv c.γ s * Complex.exp (-(windingPrimitive c x s))) := by
        rw [show (c.γ s - x)
              * (Complex.exp (-(windingPrimitive c x s)) * (-(deriv c.γ s / (c.γ s - x))))
            = -(Complex.exp (-(windingPrimitive c x s))
                * ((c.γ s - x) * (deriv c.γ s / (c.γ s - x)))) from by ring,
            hmul]
        ring
      rw [key]
      ring
    rw [hzero] at h4
    exact h4
  have hdiff : Differentiable ℝ
      (fun s : ℝ => (c.γ s - x) * Complex.exp (-(windingPrimitive c x s))) :=
    fun s => (hderiv s).differentiableAt
  have hderiv0 : ∀ s : ℝ,
      deriv (fun s : ℝ => (c.γ s - x) * Complex.exp (-(windingPrimitive c x s))) s = 0 :=
    fun s => (hderiv s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv0 t 0
  have h0 : (fun s : ℝ => (c.γ s - x) * Complex.exp (-(windingPrimitive c x s))) 0 = c.γ 0 - x := by
    simp [windingPrimitive_zero]
  exact hconst.trans h0

/-- **The primitive at a full period is an integral multiple of `2πi`.**  Evaluating the constant
produced by `windingPrimitive_const_exp` at `2π` and using `γ (2π) = γ 0`, the exponential factor
is `1`; the kernel of `exp` is `2πi ℤ`. -/
theorem windingPrimitive_int (c : SmoothPlaneCurve) {x : ℂ} (hx : x ∉ c.trace) :
    ∃ k : ℤ, windingPrimitive c x (2 * Real.pi)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hc := windingPrimitive_const_exp c hx (2 * Real.pi)
  have hper : c.γ (2 * Real.pi) = c.γ 0 := by simpa using c.periodic 0
  rw [hper] at hc
  have hz : c.γ 0 - x ≠ 0 := by
    intro h
    exact hx (sub_eq_zero.mp h ▸ c.mem_trace 0)
  have hexp : Complex.exp (-(windingPrimitive c x (2 * Real.pi))) = 1 :=
    mul_left_cancel₀ hz (by rw [mul_one]; exact hc)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨-n, ?_⟩
  have hF : windingPrimitive c x (2 * Real.pi)
      = -((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    rw [← hn]; ring
  rw [hF]; push_cast; ring

/-- **The winding integral is an integer.** -/
theorem wind_mem_int (c : SmoothPlaneCurve) {x : ℂ} (hx : x ∉ c.trace) :
    ∃ k : ℤ, wind c x = (k : ℂ) := by
  obtain ⟨k, hk⟩ := windingPrimitive_int c hx
  refine ⟨k, ?_⟩
  rw [wind_def, hk, mul_comm (k : ℂ) (2 * (Real.pi : ℂ) * Complex.I),
    inv_mul_cancel_left₀ two_pi_I_ne_zero]

end

end Work.Smooth.Jordan

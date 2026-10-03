import Mathlib

namespace Work.Fatou.Analysis

open Set Filter Metric Complex MeasureTheory intervalIntegral

/-- Derivative of the circle parametrisation `θ ↦ r * exp (θ * I)`, as the chain rule
composing the real linear map `θ ↦ θ * I` with the complex exponential. -/
private lemma hasDerivAt_exp_mul_I (r t : ℝ) :
    HasDerivAt (fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      ((r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)) t := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  have h2 : HasDerivAt (Complex.exp ∘ fun θ : ℝ => ((θ : ℂ) * Complex.I))
      (Complex.exp (↑t * Complex.I) * Complex.I) t := by
    simpa only [Function.comp_apply] using
      (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t h1
  have h3 := h2.const_mul (r : ℂ)
  simpa only [Function.comp_apply] using h3

/-- The speed of the circle parametrisation has norm `r` when `r ≥ 0`. -/
private lemma norm_exp_mul_I (r t : ℝ) (hr : 0 ≤ r) :
    ‖(r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)‖ = r := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hr]

/-- If `g` is `C¹` then the displacement of `g` along an arc of the circle of radius `r` is at
most the integral of `r * ‖fderiv ℝ g‖` along the arc.

This is the arc-length (speed) estimate `‖g (γ b) - g (γ a)‖ ≤ ∫ ‖(g ∘ γ)'‖` for
`γ θ = r * exp (θ * I)`, together with `‖γ' θ‖ = r`. -/
theorem norm_sub_le_integral_circle (g : ℂ → ℂ) (r : ℝ) (hr : 0 ≤ r) (a b : ℝ) (hab : a ≤ b)
    (hC1 : ContDiff ℝ 1 g) :
    ‖g (r * Complex.exp (b * Complex.I)) - g (r * Complex.exp (a * Complex.I))‖ ≤
      ∫ θ in a..b, r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ := by
  have hg_diff : Differentiable ℝ g := hC1.differentiable_one
  have hγcont : Continuous (fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :=
    continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
  -- derivative of `g` along the arc
  have hφderiv : ∀ t : ℝ, HasDerivAt (g ∘ fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      ((fderiv ℝ g ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)))
        ((r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I))) t := by
    intro t
    exact ((hg_diff.differentiableAt).hasFDerivAt).comp_hasDerivAt t (hasDerivAt_exp_mul_I r t)
  -- the integrand dominates the speed
  have hbound : ∀ t : ℝ,
      ‖(fderiv ℝ g ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)))
          ((r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I))‖
        ≤ r * ‖fderiv ℝ g ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))‖ := by
    intro t
    calc ‖(fderiv ℝ g ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)))
            ((r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I))‖
        ≤ ‖fderiv ℝ g ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))‖ *
            ‖(r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))‖ * r := by
          rw [norm_exp_mul_I r t hr]
      _ = r * ‖fderiv ℝ g ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))‖ := by ring
  have hφcont : Continuous (g ∘ fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :=
    hC1.continuous.comp hγcont
  have hBcont : Continuous
      (fun θ : ℝ => r * ‖fderiv ℝ g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) :=
    continuous_const.mul (continuous_norm.comp ((hC1.continuous_fderiv one_ne_zero).comp hγcont))
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le
    (f := g ∘ fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    (B := fun θ : ℝ => r * ‖fderiv ℝ g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
    hab hφcont.continuousOn
    (fun t _ => (hφderiv t).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall (fun t _ => by
      rw [(hφderiv t).deriv]; exact hbound t))
    hBcont.continuousOn.intervalIntegrable
  simpa [Function.comp_def] using hmain

end Work.Fatou.Analysis

import Mathlib

namespace Work.Fatou.Analysis

/-- Chain-rule bound for the circle parametrisation `θ ↦ r * exp(θ * I)`:
the derivative of `θ ↦ g (r * exp(θ * I))` at `x` is at most `r` times the operator norm of
`fderiv ℝ g` at the corresponding point. -/
theorem norm_deriv_circle_le (g : ℂ → ℂ) (r : ℝ) (hr : 0 ≤ r) (hC1 : ContDiff ℝ 1 g) (x : ℝ) :
    ‖deriv (fun θ : ℝ => g (r * Complex.exp (θ * Complex.I))) x‖ ≤
      r * ‖fderiv ℝ g (r * Complex.exp (x * Complex.I))‖ := by
  have hgdiff : Differentiable ℝ g := hC1.differentiable (by norm_num)
  have hγderiv : HasDerivAt (fun θ : ℝ => r * Complex.exp (θ * Complex.I))
      (Complex.I * (r * Complex.exp (x * Complex.I))) x := by
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h2 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I x := by
      simpa using h1.mul_const Complex.I
    have h3 : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I))
        (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x :=
      (Complex.hasDerivAt_exp ((x : ℂ) * Complex.I)).comp x h2
    have h4 := h3.const_mul (r : ℂ)
    convert h4 using 1
    ring
  have hd : deriv (fun θ : ℝ => g (r * Complex.exp (θ * Complex.I))) x =
      (fderiv ℝ g (r * Complex.exp (x * Complex.I)))
        (Complex.I * (r * Complex.exp (x * Complex.I))) :=
    (hgdiff.differentiableAt.hasFDerivAt.comp_hasDerivAt x hγderiv).deriv
  rw [hd]
  have h2 : ‖Complex.I * (r * Complex.exp (x * Complex.I))‖ = r := by
    simp [Complex.norm_exp_ofReal_mul_I, Complex.norm_I, abs_of_nonneg hr]
  calc ‖(fderiv ℝ g (r * Complex.exp (x * Complex.I)))
          (Complex.I * (r * Complex.exp (x * Complex.I)))‖
      ≤ ‖fderiv ℝ g (r * Complex.exp (x * Complex.I))‖ *
          ‖Complex.I * (r * Complex.exp (x * Complex.I))‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ g (r * Complex.exp (x * Complex.I))‖ * r := by rw [h2]
    _ = r * ‖fderiv ℝ g (r * Complex.exp (x * Complex.I))‖ := by ring

end Work.Fatou.Analysis

import Mathlib

namespace Work.GenShared

open Complex Metric

/-- If `y : ℂ → ℂ` is complex differentiable on the ball `ball x0 δ` and `z` lies in that ball
with `y z ≠ 0`, then the logarithmic derivative `w ↦ deriv y w / y w` has derivative
`deriv (deriv y) z / y z - (deriv y z / y z)^2` at `z`. -/
theorem hasDerivAt_deriv_div {y : ℂ → ℂ} {x0 : ℂ} {δ : ℝ} (hy : DifferentiableOn ℂ y (ball x0 δ))
    {z : ℂ} (hz : z ∈ ball x0 δ) (hne : y z ≠ 0) :
    HasDerivAt (fun w => deriv y w / y w) (deriv (deriv y) z / y z - (deriv y z / y z) ^ 2) z := by
  have hball : ball x0 δ ∈ nhds z := isOpen_ball.mem_nhds hz
  have hyz : DifferentiableAt ℂ y z := hy.differentiableAt hball
  have hana : AnalyticAt ℂ y z := (hy.analyticOn isOpen_ball).analyticAt hball
  have hderiv : DifferentiableAt ℂ (deriv y) z := hana.deriv.differentiableAt
  have h1 : HasDerivAt y (deriv y z) z := hyz.hasDerivAt
  have h2 : HasDerivAt (deriv y) (deriv (deriv y) z) z := hderiv.hasDerivAt
  have h3 : HasDerivAt (fun w => deriv y w / y w)
      ((deriv (deriv y) z * y z - deriv y z * deriv y z) / y z ^ 2) z := h2.div h1 hne
  convert h3 using 1
  field_simp

end Work.GenShared

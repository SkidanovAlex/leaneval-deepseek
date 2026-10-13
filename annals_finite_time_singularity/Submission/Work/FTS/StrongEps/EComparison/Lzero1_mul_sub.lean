import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

theorem Lzero1_mul_sub (f g : ℝ → ℝ) (θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (hf : Differentiable ℝ f) (hfd : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hgd : Differentiable ℝ (deriv g)) :
    Work.FTS.EllipticEst.Lzero1 (fun t => f t * g t) θ
        - f θ * Work.FTS.EllipticEst.Lzero1 g θ
      = -g θ * deriv (deriv f) θ + (Real.tan θ * g θ - 2 * deriv g θ) * deriv f θ := by
  -- `L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6` is a second-order operator, so the product rule gives
  -- `L₀(fg) - f·L₀(g) = -g·f'' + (tan θ · g - 2g')·f'`.
  have hfg : deriv (fun t => f t * g t) = fun t => deriv f t * g t + f t * deriv g t := by
    funext t; exact deriv_mul (hf t) (hg t)
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have h2 : deriv (fun t => deriv f t * g t + f t * deriv g t) θ
      = deriv (fun t => deriv f t * g t) θ + deriv (fun t => f t * deriv g t) θ :=
    deriv_fun_add (hfd θ |>.mul (hg θ)) ((hf θ).mul (hgd θ))
  have h3 : deriv (fun t => deriv f t * g t) θ
      = deriv (deriv f) θ * g θ + deriv f θ * deriv g θ := deriv_mul (hfd θ) (hg θ)
  have h4 : deriv (fun t => f t * deriv g t) θ
      = deriv f θ * deriv g θ + f θ * deriv (deriv g) θ := deriv_mul (hf θ) (hgd θ)
  have h5 : deriv (fun t => Real.tan t * (f t * g t)) θ
      = deriv Real.tan θ * (f θ * g θ) + Real.tan θ * deriv (fun t => f t * g t) θ :=
    deriv_mul htan ((hf θ).mul (hg θ))
  have h6 : deriv (fun t => Real.tan t * g t) θ
      = deriv Real.tan θ * g θ + Real.tan θ * deriv g θ := deriv_mul htan (hg θ)
  have h7 : deriv (fun t => f t * g t) θ = deriv f θ * g θ + f θ * deriv g θ :=
    deriv_mul (hf θ) (hg θ)
  rw [Work.FTS.EllipticEst.Lzero1, Work.FTS.EllipticEst.Lzero1]
  rw [hfg]
  beta_reduce
  rw [h2, h3, h4, h5, h6, h7]
  ring

end Work.FTS.StrongEps.EComparison

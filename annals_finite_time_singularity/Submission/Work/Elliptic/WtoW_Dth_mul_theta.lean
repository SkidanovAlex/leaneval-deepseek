import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- The product rule for `D_θ = sin(2θ)·∂_θ` in the angular variable, the factor
`c` depending only on `θ`: `D_θ(c(θ) h(z,θ)) = c(θ) D_θ h(z,θ) + sin(2θ) c'(θ) h(z,θ)`. -/
theorem WtoW_Dth_mul_theta (c : ℝ → ℝ) (h : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hc : DifferentiableAt ℝ c θ) (hh : DifferentiableAt ℝ (fun θ' => h z θ') θ) :
    Work.Spaces.Dth (fun z θ => c θ * h z θ) z θ
      = c θ * Work.Spaces.Dth h z θ + (Real.sin (2 * θ) * deriv c θ) * h z θ := by
  have hd : deriv (fun θ' => c θ' * h z θ') θ
      = deriv c θ * h z θ + c θ * deriv (fun θ' => h z θ') θ := by
    show deriv (c * (fun θ' => h z θ')) θ
      = deriv c θ * h z θ + c θ * deriv (fun θ' => h z θ') θ
    rw [deriv_mul hc hh]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hd]
  ring

end Work.Elliptic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

theorem pth_tan_mul (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (h : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = Ψ z θ / Real.cos θ ^ 2 + Real.tan θ * Work.Spaces.pth Ψ z θ := by
  unfold Work.Spaces.pth
  change deriv (fun θ' => Real.tan θ' * Ψ z θ') θ
    = Ψ z θ / Real.cos θ ^ 2 + Real.tan θ * deriv (fun θ' => Ψ z θ') θ
  rw [show (fun θ' => Real.tan θ' * Ψ z θ') = Real.tan * (fun θ' => Ψ z θ') from rfl]
  rw [deriv_mul ((Real.differentiableAt_tan).mpr hcos) h, Real.deriv_tan]
  ring

end Work.Elliptic

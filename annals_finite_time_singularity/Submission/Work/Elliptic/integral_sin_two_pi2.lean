import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.Elliptic

theorem integral_sin_two_pi2 (x : ℝ) :
    ∫ s in x..(π / 2), Real.sin (2 * s) = Real.cos x ^ 2 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [intervalIntegral.integral_comp_mul_left (fun y : ℝ => Real.sin y) h2]
  rw [show (2 : ℝ) * (π / 2) = π by ring]
  rw [integral_sin, Real.cos_pi, Real.cos_sq]
  rw [smul_eq_mul]
  ring

end Work.Elliptic

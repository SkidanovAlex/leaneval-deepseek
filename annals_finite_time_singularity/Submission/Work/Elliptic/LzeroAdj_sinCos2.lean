import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.Elliptic

set_option autoImplicit false

/-- The first derivative of the angular profile `sinCos2`: `(sin θ cos²θ)' = cos³θ - 2 sin²θ cos θ`. -/
lemma sinCos2_deriv_eq (θ : ℝ) :
    deriv sinCos2 θ = Real.cos θ ^ 3 - 2 * Real.sin θ ^ 2 * Real.cos θ := by
  unfold sinCos2
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  rw [Real.deriv_sin]
  rw [deriv_fun_pow (by fun_prop) 2]
  rw [Real.deriv_cos]
  ring_nf

/-- The derivative of the first derivative of `sinCos2`:
`(cos³θ - 2 sin²θ cos θ)' = 2 sin³θ - 7 sin θ cos²θ`. -/
lemma sinCos2_deriv_deriv_eq (θ : ℝ) :
    deriv (fun θ => Real.cos θ ^ 3 - 2 * Real.sin θ ^ 2 * Real.cos θ) θ
      = 2 * Real.sin θ ^ 3 - 7 * Real.sin θ * Real.cos θ ^ 2 := by
  rw [deriv_fun_sub (by fun_prop) (by fun_prop)]
  rw [deriv_fun_pow (by fun_prop) 3]
  rw [Real.deriv_cos]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  rw [deriv_const_mul (2 : ℝ) (by fun_prop)]
  rw [deriv_fun_pow (by fun_prop) 2]
  rw [Real.deriv_sin]
  rw [Real.deriv_cos]
  ring_nf

/-- The second derivative of the angular profile:
`(sin θ cos²θ)'' = 2 sin³θ - 7 sin θ cos²θ`. -/
lemma d2_sinCos2 (θ : ℝ) :
    d2 sinCos2 θ = 2 * Real.sin θ ^ 3 - 7 * Real.sin θ * Real.cos θ ^ 2 := by
  have hfun : (fun φ => deriv sinCos2 φ)
      = fun φ => Real.cos φ ^ 3 - 2 * Real.sin φ ^ 2 * Real.cos φ := by
    funext φ; exact sinCos2_deriv_eq φ
  unfold d2
  rw [hfun]
  exact sinCos2_deriv_deriv_eq θ

/-- `sin θ cos²θ` lies in the kernel of the formal adjoint `L₀*` of the `α = 0` elliptic
operator, on the set where `tan θ` is defined. -/
lemma LzeroAdj_sinCos2 (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.LzeroAdj Work.Elliptic.sinCos2 θ = 0 := by
  rw [LzeroAdj, d2_sinCos2, sinCos2_deriv_eq, Real.tan_eq_sin_div_cos]
  unfold sinCos2
  field_simp
  ring

end Work.Elliptic

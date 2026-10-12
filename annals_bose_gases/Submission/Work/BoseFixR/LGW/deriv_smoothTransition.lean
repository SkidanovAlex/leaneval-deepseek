import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Module.ModuleTopology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Real Filter
open scoped Topology

namespace Work.BoseFixR.LGW

/-- On `(0,1)` the smooth transition function rewrites as the logistic function
`1/(1 + exp (1/y - 1/(1-y)))` of the rescaled variable. -/
theorem smoothTransition_eq_inv_one_add_exp {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    Real.smoothTransition y = (1 + Real.exp (y⁻¹ - (1-y)⁻¹))⁻¹ := by
  have hy1' : 0 < 1 - y := by linarith
  rw [Real.smoothTransition, expNegInvGlue, if_neg (not_le.2 hy0), expNegInvGlue,
    if_neg (not_le.2 hy1')]
  have hfac : Real.exp (-(1-y)⁻¹) = Real.exp (y⁻¹ - (1-y)⁻¹) * Real.exp (-y⁻¹) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hfac]
  field_simp

theorem deriv_smoothTransition {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    deriv Real.smoothTransition x =
      Real.exp (1/x - 1/(1-x)) / (1 + Real.exp (1/x - 1/(1-x)))^2 * (1/x^2 + 1/(1-x)^2) := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1x : (1 - x) ≠ 0 := by linarith
  -- derivatives of the two elementary pieces
  have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x^2)⁻¹) x := hasDerivAt_inv hxne
  have h2 : HasDerivAt (fun y : ℝ => (1-y)⁻¹) (((1-x)^2)⁻¹) x := by
    have hh := (hasDerivAt_inv h1x).comp x ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    have hh' : HasDerivAt (fun y : ℝ => (1-y)⁻¹) (-((1-x)^2)⁻¹ * (0-1)) x := hh
    simpa only [zero_sub, neg_mul_neg, mul_one] using hh'
  have hφ : HasDerivAt (fun y : ℝ => y⁻¹ - (1-y)⁻¹) (-(x^2)⁻¹ - ((1-x)^2)⁻¹) x :=
    h1.sub h2
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (y⁻¹ - (1-y)⁻¹))
      (Real.exp (x⁻¹ - (1-x)⁻¹) * (-(x^2)⁻¹ - ((1-x)^2)⁻¹)) x := hφ.exp
  have h1a := hexp.const_add 1
  have hfin := h1a.inv (by positivity)
  -- derivative of the rewritten function
  have hderiv : HasDerivAt (fun y : ℝ => (1 + Real.exp (y⁻¹ - (1-y)⁻¹))⁻¹)
      (Real.exp (x⁻¹ - (1-x)⁻¹) / (1 + Real.exp (x⁻¹ - (1-x)⁻¹))^2 *
        ((x^2)⁻¹ + ((1-x)^2)⁻¹)) x := by
    refine hfin.congr_deriv ?_
    rw [show -(Real.exp (x⁻¹ - (1-x)⁻¹) * (-(x^2)⁻¹ - ((1-x)^2)⁻¹))
        = Real.exp (x⁻¹ - (1-x)⁻¹) * ((x^2)⁻¹ + ((1-x)^2)⁻¹) by ring]
    rw [div_mul_eq_mul_div]
  -- the two functions agree on the open interval, a neighbourhood of `x`
  have heq : Real.smoothTransition =ᶠ[𝓝 x]
      (fun y : ℝ => (1 + Real.exp (y⁻¹ - (1-y)⁻¹))⁻¹) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Set.Ioo (0:ℝ) 1 from ⟨hx0, hx1⟩)]
      with y hy
    exact smoothTransition_eq_inv_one_add_exp hy.1 hy.2
  have hfinal := hderiv.congr_of_eventuallyEq heq
  simpa only [one_div] using hfinal.deriv

end Work.BoseFixR.LGW

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set

namespace Work.Elliptic

/-- `∫_0^{π/2} sin 2θ · sin θ cos²θ dθ = 4/15`.

Substituting `u = sin θ` turns the integrand `sin 2θ · sin θ cos²θ = 2 sin²θ cos³θ`
into `(2u² - 2u⁴) du`, so the integral is `∫_0^1 (2u² - 2u⁴) du = 2/3 - 2/5 = 4/15`. -/
theorem integral_sin_two_mul_sinCos2 :
    ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ = 4 / 15 := by
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  rw [hIθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
  -- rewrite the integrand in the form `(g ∘ sin) θ * cos θ` with `g u = 2u² - 2u⁴`
  have hpt : ∀ θ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ
      = ((fun u : ℝ => 2 * u ^ 2 - 2 * u ^ 4) ∘ Real.sin) θ * Real.cos θ := by
    intro θ
    simp only [Function.comp_apply]
    rw [Work.Elliptic.sinCos2, Real.sin_two_mul]
    linear_combination (2 * Real.sin θ ^ 2 * Real.cos θ) * Real.sin_sq_add_cos_sq θ
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  -- change of variables `u = sin θ`
  rw [intervalIntegral.integral_comp_mul_deriv
      (f := Real.sin) (f' := Real.cos) (g := fun u : ℝ => 2 * u ^ 2 - 2 * u ^ 4)
      (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn (by fun_prop)]
  simp only [Real.sin_zero, Real.sin_pi_div_two]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun u : ℝ => 2 * u ^ 2).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun u : ℝ => 2 * u ^ 4).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
  norm_num

end Work.Elliptic

import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped Real

namespace Work.Coercivity

/-- The angular weight `K(θ) = 3 sin θ cos²θ` integrates to `1` over `[0,π/2]`:
`∫₀^{π/2} 3 sin θ cos²θ dθ = 1`.  This is the normalisation which makes `K` a
probability-like kernel on the angular interval; it is the `α = 0` case of the
normalising constant `c(α) = ∫ Γ K`. -/
theorem integral_Itheta_K : ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ = (1 : ℝ) := by
  -- Reduce the set integral over `Iθ = [0,π/2]` to the interval integral `∫₀^{π/2}`.
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ π/2)]
  -- Fundamental theorem of calculus with the antiderivative `θ ↦ -cos³θ`.
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (π/2),
      HasDerivAt (fun θ : ℝ => - (Real.cos θ)^3) (Work.Spaces.K x) x := by
    intro x hx
    have h := ((Real.hasDerivAt_cos x).pow 3).neg
    convert h using 1
    simp only [Work.Spaces.K]; ring
  have hint : IntervalIntegrable Work.Spaces.K volume (0:ℝ) (π/2) := by
    apply Continuous.intervalIntegrable
    change Continuous (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2)
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Real.cos_pi_div_two, Real.cos_zero]
  norm_num

end Work.Coercivity

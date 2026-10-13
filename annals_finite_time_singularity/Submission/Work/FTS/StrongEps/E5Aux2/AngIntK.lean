import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.E5Aux2

/-!
# `∫_{Iθ} K θ = 1`

The angular normalisation `∫_{[0,π/2]} 3 sin θ cos²θ dθ = 1` of the paper
(`K θ = 3 sin θ cos²θ`, the weight of the `φ`-variable in the `(ρ,θ)` reduction).

The primitive of `K` is `-cos³`, since `(-cos³θ)' = 3 sin θ cos²θ`, so the integral is
`cos³ 0 - cos³ (π/2) = 1 - 0 = 1`.  The set integral over `Iθ = [0,π/2]` is converted to the
interval integral `∫_0^{π/2}` by `MeasureTheory.integral_Icc_eq_integral_Ioc` followed by
`intervalIntegral.integral_of_le` (the removed point `{0}` is null).
-/

/-- `K` is continuous, hence interval integrable. -/
theorem continuous_K : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
  unfold Work.Spaces.K
  fun_prop

/-- The primitive `-cos³` of `K θ = 3 sin θ cos²θ`. -/
theorem hasDerivAt_neg_cos_cube (x : ℝ) :
    HasDerivAt (fun θ : ℝ => -(Real.cos θ) ^ 3) (Work.Spaces.K x) x := by
  have h3 : HasDerivAt (fun θ : ℝ => -(Real.cos θ) ^ 3)
      (-(3 * (Real.cos x) ^ (3 - 1) * (-Real.sin x))) x :=
    ((Real.hasDerivAt_cos x).pow 3).neg
  convert h3 using 1
  rw [Work.Spaces.K]
  norm_num
  ring

/-- `∫_{[0,π/2]} K θ dθ = 1`, as an interval integral. -/
theorem integral_K_interval :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), Work.Spaces.K θ) = 1 := by
  have hint : IntervalIntegrable (fun θ : ℝ => Work.Spaces.K θ) volume
      (0 : ℝ) (Real.pi / 2) := continuous_K.intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_neg_cos_cube x) hint
  rw [h]
  simp [Real.cos_pi_div_two, Real.cos_zero]

theorem AngIntK : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ) = 1 := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
  rw [hIθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpi]
  exact integral_K_interval

end Work.FTS.StrongEps.E5Aux2

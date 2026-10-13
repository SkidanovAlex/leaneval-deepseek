import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.Spaces

/-- The `H^0`-weight `w/ sin(2θ)^{η/2}` is dominated by the `W^{0,∞}`-weight
`W = w · w_θ = w · sin(2θ)^{-γ/2}`: since `η = 99/100 < 1 < γ = 1 + α/10` and
`0 ≤ sin(2θ) ≤ 1` on `[0,π/2]`, the exponent `-η/2` is the larger one, and a base
in `[0,1]` is smaller with the larger exponent. -/
theorem H_le_Wt (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  rw [Wt, wTheta]
  -- `w z ≥ 0` always, and `s := sin(2θ) ∈ [0,1]` for `θ ∈ [0,π/2]`.
  have ha : 0 ≤ w z := by rw [w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  -- Since `-η/2 ≥ -γ/2` and `sin(2θ) ∈ [0,1]`, we have `sin(2θ)^{-η/2} ≤ sin(2θ)^{-γ/2}`.
  have hkey : 1 / (Real.sin (2 * θ)) ^ (eta / 2) ≤ (Real.sin (2 * θ)) ^ (-(gam α / 2)) := by
    have h1 : 1 / (Real.sin (2 * θ)) ^ (eta / 2) = (Real.sin (2 * θ)) ^ (-(eta / 2)) := by
      rw [one_div, ← Real.rpow_neg hs0]
    rw [h1]
    apply Real.rpow_le_rpow_of_exponent_ge_of_imp hs0 hs1
    · have hgam : eta ≤ gam α := by linarith [one_lt_gam hα, eta_lt_one]
      linarith
    · intro _ hy
      exact absurd hy (by norm_num [eta])
  -- Multiply by `w z ≥ 0` and square (both sides are nonnegative).
  calc (w z / (Real.sin (2 * θ)) ^ (eta / 2)) ^ 2
      = (w z * (1 / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by rw [div_eq_mul_one_div]
    _ ≤ (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2 := by
        apply pow_le_pow_left₀ _ _ 2
        · exact mul_nonneg ha (div_nonneg zero_le_one (Real.rpow_nonneg hs0 _))
        · exact mul_le_mul_of_nonneg_left hkey ha

end Work.Spaces

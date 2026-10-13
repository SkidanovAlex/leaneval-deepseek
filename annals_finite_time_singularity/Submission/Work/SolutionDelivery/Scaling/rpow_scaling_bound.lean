import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling

/-- Pointwise scaling bound for the `α`-power vorticity decay `C/(‖x‖^α + 1)` under the
Euler rescaling `x ↦ λx`: the factor `|λ|^α` produced by `(‖λx‖)^α` is absorbed into the
constant, at the price of the multiplicative factor `(|λ|^{-α} + 1)`. -/
theorem rpow_scaling_bound {α : NNReal} {c lam r : ℝ} (hlam : lam ≠ 0) (hc : 0 < c) (hr : 0 ≤ r) :
    lam ^ 2 * (c / ((|lam| * r) ^ (α : ℝ) + 1))
      ≤ lam ^ 2 * c * (|lam| ^ (-(α : ℝ)) + 1) / (r ^ (α : ℝ) + 1) := by
  have habs : 0 < |lam| := abs_pos.mpr hlam
  have habs0 : 0 ≤ |lam| := le_of_lt habs
  have hArg0 : 0 ≤ |lam| * r := mul_nonneg habs0 hr
  -- positivity of the two denominators
  have hA : 0 < (|lam| * r) ^ (α : ℝ) + 1 := by
    have := Real.rpow_nonneg hArg0 (α : ℝ); linarith
  have hC : 0 < r ^ (α : ℝ) + 1 := by
    have := Real.rpow_nonneg hr (α : ℝ); linarith
  -- `|λ|^{-α} · |λ|^{α} = 1`
  have hpa : |lam| ^ (-(α : ℝ)) * |lam| ^ (α : ℝ) = 1 := by
    rw [← Real.rpow_add habs (-(α : ℝ)) (α : ℝ), neg_add_cancel, Real.rpow_zero]
  -- `|λ|^{-α} · (|λ| r)^{α} = r^{α}`
  have hpt : |lam| ^ (-(α : ℝ)) * (|lam| * r) ^ (α : ℝ) = r ^ (α : ℝ) := by
    rw [Real.mul_rpow habs0 hr, ← mul_assoc, hpa, one_mul]
  have hp0 : 0 ≤ |lam| ^ (-(α : ℝ)) := Real.rpow_nonneg habs0 _
  have ht0 : 0 ≤ (|lam| * r) ^ (α : ℝ) := Real.rpow_nonneg hArg0 _
  -- the cross-multiplied core inequality `r^α + 1 ≤ (|λ|^{-α} + 1) ((|λ| r)^α + 1)`
  have key : r ^ (α : ℝ) + 1 ≤ (|lam| ^ (-(α : ℝ)) + 1) * ((|lam| * r) ^ (α : ℝ) + 1) := by
    nlinarith [hpt, hp0, ht0]
  have hcore : 1 / ((|lam| * r) ^ (α : ℝ) + 1) ≤ (|lam| ^ (-(α : ℝ)) + 1) / (r ^ (α : ℝ) + 1) := by
    rw [div_le_div_iff₀ hA hC]; simpa using key
  -- multiply by the nonnegative factor `λ² c`
  have hpos : 0 ≤ lam ^ 2 * c := mul_nonneg (sq_nonneg lam) (le_of_lt hc)
  have step2 := mul_le_mul_of_nonneg_left hcore hpos
  simpa [div_eq_mul_inv, mul_assoc, mul_div_assoc] using step2

end Work.SolutionDelivery.Scaling

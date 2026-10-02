import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.nibble_state

namespace Work.Deep.Nibble

/-- For `0 ≤ x ≤ 1/2` we have `log (1 - x) ≥ -2 * x`.

Proof: `(1 + 2x)(1 - x) = 1 + x(1 - 2x) ≥ 1`, so by monotonicity of `log`,
`0 = log 1 ≤ log ((1+2x)(1-x)) = log (1+2x) + log (1-x)`.
Since `log (1+2x) ≤ (1+2x) - 1 = 2x` (tangent-line bound at `1`),
it follows that `log (1-x) ≥ -2x`. -/
theorem log_one_sub_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have h1x : 0 < 1 - x := by linarith
  have h2pos : 0 < 1 + 2 * x := by linarith
  have h2x : 2 * x ≤ 1 := by linarith
  -- the key algebraic bound: `(1 + 2x) * (1 - x) ≥ 1`, i.e. `2x² ≤ x`
  have h4 : 0 ≤ x * (1 - 2 * x) := mul_nonneg hx0 (sub_nonneg.mpr h2x)
  have hgoal : 1 ≤ (1 + 2 * x) * (1 - x) := by
    have e : (1 + 2 * x) * (1 - x) = 1 + x * (1 - 2 * x) := by ring
    rw [e]
    linarith
  -- take logs and expand the product
  have hmono : 0 ≤ Real.log (1 + 2 * x) + Real.log (1 - x) := by
    have h := Real.log_le_log zero_lt_one hgoal
    rwa [Real.log_one, Real.log_mul (ne_of_gt h2pos) (ne_of_gt h1x)] at h
  -- tangent-line bound `log y ≤ y - 1` at `y = 1 + 2x`
  have hlog : Real.log (1 + 2 * x) ≤ 2 * x := by
    have h := Real.log_le_sub_one_of_pos h2pos
    linarith
  linarith

end Work.Deep.Nibble

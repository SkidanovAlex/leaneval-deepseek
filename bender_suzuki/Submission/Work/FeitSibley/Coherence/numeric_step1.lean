import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.FeitSibley.Coherence

/-- Key numeric inequality: for `d ≥ 1` and `t ≥ d + 1`, one has
`4 d² t < (t (d+1) - 1)²`. -/
theorem key_ineq {d t : ℝ} (hd : 1 ≤ d) (ht : d + 1 ≤ t) :
    4*d^2*t < (t*(d+1) - 1)^2 := by
  nlinarith [sq_nonneg (t - (d + 1)), hd, ht]

theorem numeric_step1 {d x z : ℝ} (hd : 1 ≤ d) (hx : 1 < x) (hz : 1 ≤ z)
    (hx1 : (x - 1)^2 ≤ 4*d^2*(x/z)) (hz1 : d + 1 ≤ z) (hx2 : d + 1 ≤ x/z) : False := by
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have htpos : 0 < x / z := by linarith
  -- The key inequality on `t = x/z`.
  have hkey : 4*d^2*(x/z) < ((x/z)*(d+1) - 1)^2 := key_ineq hd hx2
  -- Recover `x = (x/z) * z`.
  have hx_eq : x = (x/z)*z := by
    rw [div_mul_cancel₀ x (ne_of_gt hzpos)]
  -- `(x/z)*(d+1) - 1` is a lower bound for `x - 1`.
  have hstep : (x/z)*(d+1) - 1 ≤ x - 1 := by
    have hle : (x/z) * (d+1) ≤ x := by
      calc (x/z) * (d+1) ≤ (x/z) * z := mul_le_mul_of_nonneg_left hz1 (le_of_lt htpos)
        _ = x := hx_eq.symm
    linarith
  -- It is also nonnegative (so squaring preserves the inequality).
  have hnn : 0 ≤ (x/z)*(d+1) - 1 := by
    nlinarith [hx2, hd]
  have hsq : ((x/z)*(d+1) - 1)^2 ≤ (x - 1)^2 := by
    nlinarith [mul_self_le_mul_self hnn hstep]
  linarith [hx1, hkey, hsq]

end Work.FeitSibley.Coherence

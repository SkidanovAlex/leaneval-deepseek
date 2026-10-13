import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.FstarPkg

/-- For `0 < α ≤ 1` and `0 ≤ s ≤ 1` the weight `s²·s^{-α/5}/(α+s)` is at most `1`.
The numerator equals `s · s^{1-α/5}`: the second factor is `≤ 1` because `s ≤ 1` and
`1 - α/5 ≥ 0`, so the numerator is `≤ s ≤ α + s`, and the denominator is positive. -/
theorem sinWeight_le_one (α s : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ 2 * s ^ (-(α / 5)) / (α + s) ≤ 1 := by
  have hden : 0 < α + s := by linarith
  rcases eq_or_lt_of_le hs0 with h | hs
  · -- `s = 0`: the numerator vanishes.
    subst h
    norm_num
  · -- `0 < s`: merge the two real powers.
    have h1 : s * s ^ (-(α / 5)) = s ^ (1 - α / 5) := by
      have hh : s ^ (1 : ℝ) * s ^ (-(α / 5)) = s ^ (1 - α / 5) := by
        rw [← Real.rpow_add hs]
        ring_nf
      rwa [Real.rpow_one s] at hh
    have h2 : s ^ 2 * s ^ (-(α / 5)) = s * (s * s ^ (-(α / 5))) := by ring
    rw [div_le_one hden, h2, h1]
    have hb : s ^ (1 - α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 (by linarith)
    have hmul : s * s ^ (1 - α / 5) ≤ s := by
      calc s * s ^ (1 - α / 5) ≤ s * 1 :=
            mul_le_mul_of_nonneg_left hb (le_of_lt hs)
        _ = s := by ring
    linarith

end Work.FTS.Nonlinear.FstarPkg

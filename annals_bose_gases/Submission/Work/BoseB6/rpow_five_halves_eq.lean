import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB6

theorem rpow_five_halves_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x * y) ^ (5 / 2 : ℝ) = x ^ 2 * y * Real.sqrt (x * y ^ 3) := by
  have hxy : 0 < x * y := mul_pos hx hy
  have h1 : (x * y) ^ (5 / 2 : ℝ) = (x * y) ^ 2 * Real.sqrt (x * y) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hxy, Real.rpow_two,
      Real.sqrt_eq_rpow]
  have h2 : Real.sqrt (x * y ^ 3) = y * Real.sqrt (x * y) := by
    rw [show x * y ^ 3 = y ^ 2 * (x * y) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hy.le]
  rw [h1, h2]
  ring

end Work.BoseB6

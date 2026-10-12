import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

/-- The right-hand side rewrites to `256 * π * √3 * h^3`, since
`(4 * h * √3)^3 / 3 = 64 * h^3 * (√3)^3 / 3 = 64 * h^3 * √3`. -/
private lemma rhs_eq (h : ℝ) :
    4 * Real.pi * (4 * h * Real.sqrt 3) ^ 3 / 3
      = 256 * Real.pi * Real.sqrt 3 * h ^ 3 := by
  have hs3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [mul_pow, mul_pow, hs3]; ring

theorem arith_card512 {h c : ℝ} (hh : 0 < h) (hc : c ≤ 512) :
    c * h ^ 3 ≤ 4 * Real.pi * (4 * h * Real.sqrt 3) ^ 3 / 3 := by
  rw [rhs_eq]
  have h3 : (0 : ℝ) ≤ h ^ 3 := by positivity
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hkey : (512 : ℝ) ≤ 256 * Real.pi * Real.sqrt 3 := by
    nlinarith [Real.pi_gt_three, hsqrt]
  nlinarith [h3, hc, hkey]

end Work.BoseBox.LatticeModel

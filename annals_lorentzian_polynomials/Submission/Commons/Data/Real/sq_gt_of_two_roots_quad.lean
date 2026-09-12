import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic

namespace Commons.Data.Real

open Set

set_option autoImplicit false

theorem sq_gt_of_two_roots_quad (a c d : ℝ) (ha : 0 < a)
    (hxy : ∃ x y : ℝ, x ≠ y ∧ a * x ^ 2 - 2 * c * x + d = 0 ∧ a * y ^ 2 - 2 * c * y + d = 0) :
    c ^ 2 > a * d := by
  rcases hxy with ⟨x, y, hne, hx, hy⟩
  have hxyn : x - y ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  -- From the two root equations, subtract to get a * (x + y) = 2 * c.
  have hdiff : a * (x ^ 2 - y ^ 2) - 2 * c * (x - y) = 0 := by nlinarith
  have hfac : (x - y) * (a * (x + y) - 2 * c) = 0 := by nlinarith
  have hc0 : a * (x + y) - 2 * c = 0 := by
    rcases mul_eq_zero.mp hfac with hsub | hterm
    · exact False.elim (hxyn hsub)
    · exact hterm
  have hc : 2 * c = a * (x + y) := by linarith
  -- Using x as a root and 2 * c = a * (x + y), get d = a * x * y.
  have hcx : a * (x + y) * x = 2 * c * x := by rw [← hc]
  have hd : d = a * x * y := by
    have hx2 : a * x ^ 2 - a * (x + y) * x + d = 0 := by
      simpa [← hcx] using hx
    nlinarith
  -- 4 * (c ^ 2 - a * d) = a ^ 2 * (x - y) ^ 2 > 0.
  have hmain : 4 * (c ^ 2 - a * d) = a ^ 2 * (x - y) ^ 2 := by
    calc
      4 * (c ^ 2 - a * d) = (2 * c) ^ 2 - 4 * a * d := by ring
      _ = (a * (x + y)) ^ 2 - 4 * a * (a * x * y) := by rw [hc, hd]
      _ = a ^ 2 * (x - y) ^ 2 := by ring
  have hmainpos : 0 < 4 * (c ^ 2 - a * d) := by
    rw [hmain]
    exact mul_pos (sq_pos_of_ne_zero (ne_of_gt ha)) (sq_pos_of_ne_zero hxyn)
  have hz : 0 < c ^ 2 - a * d := by nlinarith
  linarith

end Commons.Data.Real
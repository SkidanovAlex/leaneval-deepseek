import Mathlib

namespace Work.CKFinal.Socket

/-- Membership lemma for the "lens" region of the Cohn–Kumar–Miller–Radchenko–Viazovska
interpolation argument: if `x < 1` and `x` is within `min (y^2) 1 / 4` of `1`, then `x`
lies in `(-1, 1)` and both points `(x ∓ 1/2, y)` lie outside the disk of radius `1/2`
about the origin. -/
theorem lens_mem (x y : ℝ) (hy : 0 < y) (hx : x < 1) (h : |x - 1| < min (y ^ 2) 1 / 4) :
    -1 < x ∧ x < 1 ∧ 1 / 4 < (x - 1 / 2) ^ 2 + y ^ 2 ∧
      1 / 4 < (x + 1 / 2) ^ 2 + y ^ 2 := by
  -- `|x - 1| < min (y^2) 1 / 4 ≤ 1/4`
  have h4 : min (y ^ 2) 1 / 4 ≤ 1 / 4 := by
    have := min_le_right (y ^ 2) (1 : ℝ); linarith
  have h1 : |x - 1| < 1 / 4 := lt_of_lt_of_le h h4
  -- `|x - 1| < min (y^2) 1 / 4 ≤ y^2/4`
  have hy4 : min (y ^ 2) 1 / 4 ≤ y ^ 2 / 4 := by
    have := min_le_left (y ^ 2) (1 : ℝ); linarith
  have h2 : |x - 1| < y ^ 2 / 4 := lt_of_lt_of_le h hy4
  -- hence `3/4 < x`
  have hx34 : 3 / 4 < x := by
    have := (abs_lt.mp h1).1; linarith
  -- and, since `x < 1`, `1 - x = |x - 1| < y^2/4`
  have hltx : 1 - x < y ^ 2 / 4 := by
    rw [abs_of_neg (by linarith : x - 1 < 0)] at h2; linarith
  refine ⟨by linarith, hx, ?_, ?_⟩
  · -- `(x - 1/2)^2 + y^2 - 1/4 = y^2 - x(1-x) > 0`
    nlinarith [hy, sq_nonneg y, sq_nonneg (1 - x)]
  · -- `x + 1/2 > 5/4 > 1`, so `(x + 1/2)^2 > 1 > 1/4`
    nlinarith [hy, sq_nonneg y, sq_nonneg (x + 1 / 2)]

end Work.CKFinal.Socket

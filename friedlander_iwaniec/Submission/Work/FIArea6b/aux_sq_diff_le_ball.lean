import Mathlib

namespace Work.FIArea6b

/-- The diameter bound: two points of the closed disc of radius `R` are at
squared distance at most `(2R)^2`. -/
theorem aux_sq_diff_le_ball (x1 x2 y1 y2 R : ℝ) (hR : 0 ≤ R)
    (h1 : x1^2 + y1^2 ≤ R^2) (h2 : x2^2 + y2^2 ≤ R^2) :
    (x1-x2)^2 + (y1-y2)^2 ≤ (2*R)^2 := by
  nlinarith [hR, sq_nonneg (x1 + x2), sq_nonneg (y1 + y2)]

end Work.FIArea6b

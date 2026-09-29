import Mathlib

namespace Work.C17

/-- Uniqueness of a square root: if `F` and `G` are both square roots of the same power
series `1/P` (equivalently `F²P = G²P = 1`) and both have constant coefficient `1`,
then `F = G`.

The proof uses that `PowerSeries ℝ` is an integral domain: `F² = G²` gives
`(F-G)(F+G) = 0`, and `F + G ≠ 0` because its constant coefficient is `2 ≠ 0`. -/
theorem sqrt_unique {F G P : PowerSeries ℝ}
    (hF : F ^ 2 * P = 1) (hG : G ^ 2 * P = 1)
    (hF0 : PowerSeries.constantCoeff F = 1) (hG0 : PowerSeries.constantCoeff G = 1) : F = G := by
  -- `F² = G²`, obtained by rewriting `1 = G² * P` and `1 = F² * P`.
  have hsq : F ^ 2 = G ^ 2 := by
    calc F ^ 2 = F ^ 2 * 1 := by rw [mul_one]
    _ = F ^ 2 * (G ^ 2 * P) := by rw [hG]
    _ = (F ^ 2 * G ^ 2) * P := by rw [mul_assoc]
    _ = (G ^ 2 * F ^ 2) * P := by rw [mul_comm (F ^ 2) (G ^ 2)]
    _ = G ^ 2 * (F ^ 2 * P) := by rw [mul_assoc]
    _ = G ^ 2 * 1 := by rw [hF]
    _ = G ^ 2 := by rw [mul_one]
  -- Factor: `(F - G)(F + G) = F² - G² = 0`.
  have hzero : (F - G) * (F + G) = 0 := by
    have h : (F - G) * (F + G) = F ^ 2 - G ^ 2 := by ring
    rw [h, hsq, sub_self]
  -- `F + G ≠ 0` since its constant coefficient is `1 + 1 = 2`.
  have hFG : F + G ≠ 0 := by
    intro h
    have hc := congrArg PowerSeries.constantCoeff h
    simp only [map_add, map_zero, hF0, hG0] at hc
    norm_num at hc
  -- Integral domain: a product is zero, so one factor is zero.
  rcases mul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hFG

end Work.C17

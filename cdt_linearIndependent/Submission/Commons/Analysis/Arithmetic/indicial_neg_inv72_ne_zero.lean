import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star

namespace Commons.Analysis.Arithmetic

/-- The indicial polynomial `-x⁴ + 9x³ - 29x² + 39x - 18` in the form appearing in the
Calegari–Dimitrov–Tang paper factors as `-(x-1)(x-2)(x-3)²`.  For an integer `N ≤ 0`
none of the factors vanishes, so the value is nonzero. -/
theorem indicial_neg_inv72_ne_zero (N : ℤ) (hN : N ≤ 0) :
    (-18 : ℚ) + 18 * (N : ℚ) + (-9) * ((N : ℚ) * ((N : ℚ) - 1))
      + 3 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
      + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) ≠ 0 := by
  have hx : (N : ℚ) ≤ 0 := by exact_mod_cast hN
  have h1 : (N : ℚ) - 1 ≠ 0 := by intro h; linarith
  have h2 : (N : ℚ) - 2 ≠ 0 := by intro h; linarith
  have h3 : (N : ℚ) - 3 ≠ 0 := by intro h; linarith
  have key : (-18 : ℚ) + 18 * (N : ℚ) + (-9) * ((N : ℚ) * ((N : ℚ) - 1))
      + 3 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
      + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3))
      = -(((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3) * ((N : ℚ) - 3)) := by ring
  rw [key]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h3)

end Commons.Analysis.Arithmetic
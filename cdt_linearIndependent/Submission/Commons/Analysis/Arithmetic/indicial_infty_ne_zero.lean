import Mathlib

namespace Commons.Analysis.Arithmetic

/-- For an integer `N ≥ 5`, the degree-4 indicial polynomial
`-144 + 108N - 38N(N-1) + 8N(N-1)(N-2) - N(N-1)(N-2)(N-3)`
does not vanish.  Indeed it factors as `-((N-3)(N-4))²`, and for `N ≥ 5`
both `N-3` and `N-4` are positive, so the product is positive and hence the
square is nonzero. -/
theorem indicial_infty_ne_zero (N : ℤ) (hN : 5 ≤ N) :
    (-144 : ℚ) + 108 * (N : ℚ) + (-38) * ((N : ℚ) * ((N : ℚ) - 1))
      + 8 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
      + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) ≠ 0 := by
  have h5 : (5 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have h3 : (0 : ℚ) < (N : ℚ) - 3 := by linarith
  have h4 : (0 : ℚ) < (N : ℚ) - 4 := by linarith
  have hprod : (0 : ℚ) < ((N : ℚ) - 3) * ((N : ℚ) - 4) := mul_pos h3 h4
  have hsq : (0 : ℚ) < (((N : ℚ) - 3) * ((N : ℚ) - 4)) ^ 2 := pow_pos hprod 2
  have hid : (-144 : ℚ) + 108 * (N : ℚ) + (-38) * ((N : ℚ) * ((N : ℚ) - 1))
      + 8 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
      + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3))
      = - (((N : ℚ) - 3) * ((N : ℚ) - 4)) ^ 2 := by ring
  rw [hid]
  exact neg_ne_zero.mpr (ne_of_gt hsq)

end Commons.Analysis.Arithmetic

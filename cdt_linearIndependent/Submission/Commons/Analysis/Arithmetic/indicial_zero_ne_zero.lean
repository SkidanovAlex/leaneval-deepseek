import Mathlib

namespace Commons.Analysis.Arithmetic

/-- For an integer `N ≤ 1`, the degree-4 indicial polynomial
`-(225/4) + (189/4)N - (77/4)N(N-1) + 5N(N-1)(N-2) - N(N-1)(N-2)(N-3)`
does not vanish.  Indeed, writing `u = N - 1 ≤ 0`, the expression equals
`-u⁴ + 7u³ - (73/4)u² + 21u - 9`, whose every term is nonpositive while the
constant term is strictly negative. -/
theorem indicial_zero_ne_zero (N : ℤ) (hN : N ≤ 1) :
    (-(225 / 4) : ℚ) + (189 / 4) * (N : ℚ) + (-(77 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
      + 5 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
      + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) ≠ 0 := by
  have hNq : (N : ℚ) ≤ 1 := by exact_mod_cast hN
  have hu : (N : ℚ) - 1 ≤ 0 := by linarith
  -- Clearing the denominator `4`: the expression times `4` is a polynomial in
  -- `u = N - 1` with all terms of the same sign as `-36`.
  have h4 : (4 : ℚ) * ((-(225 / 4) : ℚ) + (189 / 4) * (N : ℚ)
        + (-(77 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
        + 5 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
        + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)))
      = -4 * ((N : ℚ) - 1) ^ 4 + 28 * ((N : ℚ) - 1) ^ 3
          - 73 * ((N : ℚ) - 1) ^ 2 + 84 * ((N : ℚ) - 1) - 36 := by
    ring
  have t1 : -4 * ((N : ℚ) - 1) ^ 4 ≤ 0 := by
    nlinarith [sq_nonneg (((N : ℚ) - 1) ^ 2)]
  have t2 : 28 * ((N : ℚ) - 1) ^ 3 ≤ 0 := by
    have h : ((N : ℚ) - 1) * ((N : ℚ) - 1) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hu (sq_nonneg ((N : ℚ) - 1))
    nlinarith [h]
  have t3 : -73 * ((N : ℚ) - 1) ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ((N : ℚ) - 1)]
  have t4 : 84 * ((N : ℚ) - 1) ≤ 0 := by
    nlinarith [hu]
  intro hzero
  have hlt : (4 : ℚ) * ((-(225 / 4) : ℚ) + (189 / 4) * (N : ℚ)
        + (-(77 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
        + 5 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
        + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3))) < 0 := by
    rw [h4]
    linarith [t1, t2, t3, t4]
  rw [hzero, mul_zero] at hlt
  exact lt_irrefl 0 hlt

end Commons.Analysis.Arithmetic

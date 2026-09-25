import Mathlib

namespace Work.LT

/-- The `v`-independent part of the exponent in `gb_star_numeric_sum`:
`k(m) * (m - k(m)) - r * k(m) + 2` with `k(m) = (m+1)/2 = ⌈m/2⌉`. -/
noncomputable def gbNumC (r m : ℕ) : ℝ :=
  (((m + 1) / 2 : ℕ) : ℝ) * ((m - (m + 1) / 2 : ℕ) : ℝ)
    - (r : ℝ) * (((m + 1) / 2 : ℕ) : ℝ) + 2

/-- The exponent in `gb_star_numeric_sum` at the maximal value `v = (r-4)/8`. -/
noncomputable def gbNumE (r m : ℕ) : ℝ := ((r : ℝ) - 4) / 8 * (m : ℝ) + gbNumC r m

lemma gbNumE_one (r : ℕ) : gbNumE r 1 = -(7:ℝ)/8 * (r:ℝ) + 3/2 := by
  norm_num [gbNumE, gbNumC]
  ring

lemma gbNumE_two (r : ℕ) : gbNumE r 2 = 2 - (3:ℝ)/4 * (r:ℝ) := by
  norm_num [gbNumE, gbNumC]
  ring

end Work.LT

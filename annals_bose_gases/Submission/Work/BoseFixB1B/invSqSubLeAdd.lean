import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

/-- Elementary real inequality: for `0 < c` and `2c ≤ r` one has
`(r - c)⁻² ≤ r⁻² + 8c/r³`.  (With `t = c/r ≤ 1/2` this is `1/(1-t)² ≤ 1 + 8t`;
after clearing denominators it is `c (6r² - 15rc + 8c²) ≥ 0`, where
`6r² - 15rc + 8c² = 2c² + 3(2r - c)(r - 2c) ≥ 0`.) -/
theorem invSqSubLeAdd {c r : ℝ} (hc : 0 < c) (h2c : 2 * c ≤ r) :
    1 / (r - c) ^ 2 ≤ 1 / r ^ 2 + 8 * c / r ^ 3 := by
  have hr : 0 < r := by linarith
  have hrc : 0 < r - c := by linarith
  -- clearing denominators: `6r² - 15rc + 8c² = 2c² + 3(2r - c)(r - 2c) ≥ 0`
  have hnum : 0 ≤ 6 * r ^ 2 - 15 * r * c + 8 * c ^ 2 := by
    have h1 : 0 ≤ r - 2 * c := by linarith
    have h2 : 0 ≤ 2 * r - c := by linarith
    nlinarith [mul_nonneg h1 h2]
  have key : 0 ≤ c * (6 * r ^ 2 - 15 * r * c + 8 * c ^ 2) := mul_nonneg (le_of_lt hc) hnum
  have hR : 1 / r ^ 2 + 8 * c / r ^ 3 = (r + 8 * c) / r ^ 3 := by
    field_simp
  rw [hR, le_div_iff₀ (by positivity : (0 : ℝ) < r ^ 3), div_mul_eq_mul_div,
    div_le_iff₀ (by positivity : (0 : ℝ) < (r - c) ^ 2)]
  nlinarith [key]

end Work.BoseFixB1B

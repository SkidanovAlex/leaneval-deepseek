import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.NumberTheory.Robin

/-- Lower bound for the (truncated) power series of `1/(2 (1-y)^2) - 1/2`:
for `0 ≤ y < 1`,
`(3/2) y² + 2 y³ + (5/2) y⁴ + 3 y⁵ ≤ (1/2) (1/(1-y)² - (1+2y))`.
The difference of the two sides equals `y⁶ (7-6y) / (2 (1-y)²) ≥ 0`. -/
private lemma key_series (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (3/2:ℝ)*y^2 + 2*y^3 + (5/2)*y^4 + 3*y^5 ≤ (1/2)*(1/(1-y)^2 - (1+2*y)) := by
  have h1y : (1:ℝ) - y ≠ 0 := by linarith
  have hdiff : (1/2:ℝ)*(1/(1-y)^2 - (1+2*y)) - ((3/2:ℝ)*y^2 + 2*y^3 + (5/2)*y^4 + 3*y^5)
      = (1/2:ℝ)*y^6*(7-6*y)/(1-y)^2 := by
    field_simp
    ring
  rw [← sub_nonneg, hdiff]
  have hy76 : (0:ℝ) ≤ 7 - 6*y := by linarith
  have hnum : (0:ℝ) ≤ (1/2)*y^6*(7-6*y) := by
    have hy6 : (0:ℝ) ≤ y^6 := pow_nonneg hy0 6
    exact mul_nonneg (by positivity) hy76
  have hden : (0:ℝ) ≤ (1-y)^2 := by positivity
  exact div_nonneg hnum hden

theorem caXi2_lower_A_ge (L β bA : ℝ) (hL : 0 < L) (hβL : β < L) (hbA0 : 0 ≤ bA)
    (hbAβ : bA ≤ β) :
    3 * bA ^ 2 / (2 * L) + 2 * bA ^ 3 / L ^ 2 + 5 * bA ^ 4 / (2 * L ^ 3) + 3 * bA ^ 5 / L ^ 4
      + bA / L + bA ^ 2 / (2 * L ^ 2) + bA ^ 3 / (3 * L ^ 3) + bA ^ 4 / (4 * L ^ 4)
    ≤ L / (2 * (1 - β / L) ^ 2) - (L + 2 * β) / 2
      + (β / L + (β / L) ^ 2 / 2 + (β / L) ^ 3 / 3 + (β / L) ^ 4 / 4
          + (β / L) ^ 5 / 5 + (β / L) ^ 6 / 6) := by
  have hβ0 : 0 ≤ β := le_trans hbA0 hbAβ
  -- Step 1: the left-hand side is monotone in `bA` on `[0, ∞)`.
  have hstep1 : 3 * bA ^ 2 / (2 * L) + 2 * bA ^ 3 / L ^ 2 + 5 * bA ^ 4 / (2 * L ^ 3) + 3 * bA ^ 5 / L ^ 4
      + bA / L + bA ^ 2 / (2 * L ^ 2) + bA ^ 3 / (3 * L ^ 3) + bA ^ 4 / (4 * L ^ 4)
    ≤ 3 * β ^ 2 / (2 * L) + 2 * β ^ 3 / L ^ 2 + 5 * β ^ 4 / (2 * L ^ 3) + 3 * β ^ 5 / L ^ 4
      + β / L + β ^ 2 / (2 * L ^ 2) + β ^ 3 / (3 * L ^ 3) + β ^ 4 / (4 * L ^ 4) := by
    gcongr
  -- Step 2: the `β`-version is bounded by the right-hand side, via `key_series` at `y = β/L`.
  have hy0 : 0 ≤ β / L := div_nonneg hβ0 (le_of_lt hL)
  have hy1 : β / L < 1 := (div_lt_one hL).mpr hβL
  have hkey := key_series (β / L) hy0 hy1
  have h1 := mul_le_mul_of_nonneg_left hkey (le_of_lt hL)
  have e1 : L * ((3/2)*(β/L)^2 + 2*(β/L)^3 + (5/2)*(β/L)^4 + 3*(β/L)^5)
      = 3*β^2/(2*L) + 2*β^3/L^2 + 5*β^4/(2*L^3) + 3*β^5/L^4 := by
    field_simp
  have e2 : L * ((1/2)*(1/(1-β/L)^2 - (1+2*(β/L))))
      = L/(2*(1-β/L)^2) - (L+2*β)/2 := by
    field_simp
  rw [e1, e2] at h1
  have hβ5 : (0:ℝ) ≤ β^5/(5*L^5) := div_nonneg (pow_nonneg hβ0 5) (by positivity)
  have hβ6 : (0:ℝ) ≤ β^6/(6*L^6) := div_nonneg (pow_nonneg hβ0 6) (by positivity)
  have h3 : β / L + (β / L) ^ 2 / 2 + (β / L) ^ 3 / 3 + (β / L) ^ 4 / 4
          + (β / L) ^ 5 / 5 + (β / L) ^ 6 / 6
      = β / L + β ^ 2 / (2 * L ^ 2) + β ^ 3 / (3 * L ^ 3) + β ^ 4 / (4 * L ^ 4)
          + β ^ 5 / (5 * L ^ 5) + β ^ 6 / (6 * L ^ 6) := by
    ring
  rw [h3]
  linarith [hstep1, h1, hβ5, hβ6]

end Commons.NumberTheory.Robin
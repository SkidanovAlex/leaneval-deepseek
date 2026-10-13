import Mathlib
import Submission.Work.WilG3.Defs

namespace Work.WilG3

-- Cardinality half of `WilkieDesign.CG.G3_affine_cover` for the concrete chart family of
-- `Submission/Work/WilG3/Defs.lean`: with `K = geoK r ε = ⌈(r+2)(-log ε)⌉ + 2` the family
-- `geoCharts r K` has at most `8(r+1)(-log ε + 2)` charts.  (`geoCharts_card_le` gives
-- `card ≤ 2K`; then `K ≤ (r+2)(-log ε) + 3`, and `r+2 ≤ 2(r+1)`.)  Only `0 < ε < 1` is needed,
-- to know `0 < -log ε` and hence `0 ≤ (r+2)(-log ε)`.
theorem GeoChartsCard (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((geoCharts r (geoK r ε)).card : ℝ) ≤ 8 * ((r : ℝ) + 1) * (-Real.log ε + 2) := by
  -- `0 < ε < 1`, so `-log ε > 0`.
  have hlog : 0 < -Real.log ε := by
    have := Real.log_neg hε hε1
    linarith
  -- `K = ⌈(r+2)(-log ε)⌉ + 2 ≤ (r+2)(-log ε) + 3`.
  have hK : ((geoK r ε : ℕ) : ℝ) ≤ ((r : ℝ) + 2) * (-Real.log ε) + 3 := by
    have hx : 0 ≤ ((r : ℝ) + 2) * (-Real.log ε) :=
      mul_nonneg (by positivity) hlog.le
    have hlt := Nat.ceil_lt_add_one hx
    simp only [geoK]
    push_cast
    linarith
  -- `card ≤ 2K`.
  have hcard : ((geoCharts r (geoK r ε)).card : ℝ) ≤ 2 * ((geoK r ε : ℕ) : ℝ) := by
    have h := geoCharts_card_le r (geoK r ε)
    have h' : ((geoCharts r (geoK r ε)).card : ℝ) ≤ ((2 * geoK r ε : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa using h'
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  -- `card ≤ 2K ≤ 2((r+2)(-log ε) + 3)`.
  have h1 : ((geoCharts r (geoK r ε)).card : ℝ)
      ≤ 2 * (((r : ℝ) + 2) * (-Real.log ε) + 3) := by linarith [hcard, hK]
  -- `2(r+2)(-log ε) ≤ 8(r+1)(-log ε)`, using `r+2 ≤ 2(r+1)` and `-log ε ≥ 0`.
  have h2 : 2 * ((r : ℝ) + 2) * (-Real.log ε) ≤ 8 * ((r : ℝ) + 1) * (-Real.log ε) := by
    have hcoef : (2 : ℝ) * ((r : ℝ) + 2) ≤ 8 * ((r : ℝ) + 1) := by
      have : (2 : ℝ) * ((r : ℝ) + 2) ≤ 4 * ((r : ℝ) + 1) := by linarith
      linarith
    exact mul_le_mul_of_nonneg_right hcoef hlog.le
  have h3 : (6 : ℝ) ≤ 16 * ((r : ℝ) + 1) := by linarith
  linarith [h1, h2, h3]

end Work.WilG3

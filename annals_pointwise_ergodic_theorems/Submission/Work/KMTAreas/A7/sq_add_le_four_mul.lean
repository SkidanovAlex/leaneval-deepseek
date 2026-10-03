import Mathlib

namespace Work.KMTAreas.A7

/-- Elementary arithmetic bound: for `c, e ≥ 1` and `W ≥ 1`,
`(e + c) ^ 2 ≤ 4 * c ^ 2 * W * e ^ 2`. -/
theorem sq_add_le_four_mul (c W e : ℝ) (hc : 1 ≤ c) (hW : 1 ≤ W) (he : 1 ≤ e) :
    (e + c) ^ 2 ≤ 4 * c ^ 2 * W * e ^ 2 := by
  nlinarith [sq_nonneg (e - c), sq_nonneg (c - 1), sq_nonneg (e - 1), sq_nonneg (W - 1),
    sq_nonneg (c * e - 1), mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr he)]

end Work.KMTAreas.A7

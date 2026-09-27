import Mathlib
import Submission.Work.EQ.hetero_leaf

set_option maxHeartbeats 1000000

namespace Work.EQ

/-- The first `Small`-estimate alone already gives the desired bound.

Writing `q = 1 - κ²` and multiplying the estimate by `2 q²` turns it into
`4·C·y²·q + 32·C²·y²/κ ≤ q²`.  Since `0 < κ ≤ 1` we have `12·C²·y² ≤ 32·C²·y²/κ`,
hence `4·C·y²·q + 12·C²·y² ≤ q²`, which after multiplying by `/ (3 q²)` is exactly
`(4/3)·(C·y²)/q + 4·(C²·y²)/q² ≤ 1/3`. -/
theorem small_main {a : ℝ} (d : Work.EQ.LocData a) {y : ℝ} (hs : d.Small y) :
    (4 / 3) * (d.C * y ^ 2) / (1 - d.κ ^ 2)
      + 4 * (d.C ^ 2 * y ^ 2) / (1 - d.κ ^ 2) ^ 2 ≤ 1 / 3 := by
  obtain ⟨h1, _h2⟩ := hs
  have hq : 0 < 1 - d.κ ^ 2 := d.one_sub_sq_pos
  have hqne : (1 - d.κ ^ 2) ≠ 0 := ne_of_gt hq
  have hkpos : 0 < d.κ := d.κpos
  have hkne : d.κ ≠ 0 := ne_of_gt hkpos
  -- Multiply the estimate by `2 q²` and clear the denominators.
  have hmul := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 2 * (1 - d.κ ^ 2) ^ 2)
  have hconv : 2 * d.C * y ^ 2 * (1 / (1 - d.κ ^ 2) + 8 * d.C / (d.κ * (1 - d.κ ^ 2) ^ 2))
        * (2 * (1 - d.κ ^ 2) ^ 2)
      = 4 * (d.C * y ^ 2) * (1 - d.κ ^ 2) + 32 * (d.C ^ 2 * y ^ 2) / d.κ := by
    field_simp
    ring
  have hkey1 : 4 * (d.C * y ^ 2) * (1 - d.κ ^ 2) + 32 * (d.C ^ 2 * y ^ 2) / d.κ
      ≤ (1 - d.κ ^ 2) ^ 2 := by
    have hrhs : (1/2 : ℝ) * (2 * (1 - d.κ ^ 2) ^ 2) = (1 - d.κ ^ 2) ^ 2 := by ring
    rw [hconv, hrhs] at hmul
    exact hmul
  -- Replace the coefficient `32/κ` by `12` using `κ ≤ 1`.
  have h32 : (12 : ℝ) ≤ 32 / d.κ := by
    rw [le_div_iff₀ hkpos]
    nlinarith [d.κlt]
  have hkey : 4 * (d.C * y ^ 2) * (1 - d.κ ^ 2) + 12 * (d.C ^ 2 * y ^ 2) ≤ (1 - d.κ ^ 2) ^ 2 := by
    have hC2y : 0 ≤ d.C ^ 2 * y ^ 2 := by positivity
    have step : 12 * (d.C ^ 2 * y ^ 2) ≤ (32 / d.κ) * (d.C ^ 2 * y ^ 2) :=
      mul_le_mul_of_nonneg_right h32 hC2y
    have step3 : (32 / d.κ) * (d.C ^ 2 * y ^ 2) = 32 * (d.C ^ 2 * y ^ 2) / d.κ := by ring
    linarith [hkey1, step, step3]
  -- Put the goal over the common positive denominator `3 q²`.
  have hid : (4 / 3) * (d.C * y ^ 2) / (1 - d.κ ^ 2)
        + 4 * (d.C ^ 2 * y ^ 2) / (1 - d.κ ^ 2) ^ 2
      = (4 * (d.C * y ^ 2) * (1 - d.κ ^ 2) + 12 * (d.C ^ 2 * y ^ 2))
          / (3 * (1 - d.κ ^ 2) ^ 2) := by
    field_simp
    ring
  rw [hid, div_le_iff₀ (by positivity : (0:ℝ) < 3 * (1 - d.κ ^ 2) ^ 2)]
  nlinarith [hkey]

end Work.EQ

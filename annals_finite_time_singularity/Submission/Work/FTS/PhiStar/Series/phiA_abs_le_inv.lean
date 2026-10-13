import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

/-- The explicit rational form of `𝒜φ = phiA α z` combined over the common denominator
`(1+z)^4` (from `Work.FTS.PhiStar.phiA_eq`). -/
theorem phiA_combined (α z : ℝ) (hz : z ≠ -1) :
    Work.FTS.VocabO.phiA α z
      = ((2 * α - 10) * z ^ 3 - 8 * α * z ^ 2 + (10 + 2 * α) * z) / (1 + z) ^ 4 := by
  rw [Work.FTS.PhiStar.phiA_eq α z hz]
  field_simp
  ring

/-- **`|𝒜φ| ≤ 16/z`** for `0 < α ≤ 1`, `z > 0`: the radial profile coefficient decays like
`1/z` at infinity with a constant uniform in `α`. -/
theorem phiA_abs_le_inv (α z : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) :
    |Work.FTS.VocabO.phiA α z| ≤ 16 / z := by
  have hz1 : z ≠ -1 := by linarith
  have h4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  -- `|phiA| * z = |M z| / (1+z)^4` with `M = (2α-10)z³ - 8αz² + (10+2α)z`, so it suffices
  -- to bound `|M z| ≤ 16 (1+z)^4`.
  have hMz : |((2 * α - 10) * z ^ 3 - 8 * α * z ^ 2 + (10 + 2 * α) * z) * z|
      ≤ 16 * (1 + z) ^ 4 := by
    have key : ((2 * α - 10) * z ^ 3 - 8 * α * z ^ 2 + (10 + 2 * α) * z) * z
        = (2 * α - 10) * z ^ 4 - 8 * α * z ^ 3 + (10 + 2 * α) * z ^ 2 := by ring
    rw [key, abs_le]
    constructor
    · -- lower bound: `(2α-10)z⁴ - 8αz³ ≥ -10z⁴ - 8z³ ≥ -16(1+z)⁴`
      have h1 : (0 : ℝ) ≤ 2 * α * z ^ 4 := by positivity
      have h2 : (0 : ℝ) ≤ 8 * (1 - α) * z ^ 3 := by
        have : (0 : ℝ) ≤ 1 - α := by linarith
        positivity
      have h5 : (0 : ℝ) ≤ (10 + 2 * α) * z ^ 2 := by positivity
      have h3 : (0 : ℝ) ≤ 6 * z ^ 4 + 56 * z ^ 3 + 96 * z ^ 2 + 64 * z + 16 := by positivity
      have hexp : 16 * (1 + z) ^ 4 - 10 * z ^ 4 - 8 * z ^ 3
          = 6 * z ^ 4 + 56 * z ^ 3 + 96 * z ^ 2 + 64 * z + 16 := by ring
      nlinarith [h1, h2, h3, h5, hexp]
    · -- upper bound: `(2α-10)z⁴ - 8αz³ + (10+2α)z² ≤ 12z² ≤ 16(1+z)⁴`
      have ha : (2 * α - 10) * z ^ 4 ≤ 0 := by
        have : 2 * α - 10 ≤ 0 := by linarith
        exact mul_nonpos_of_nonpos_of_nonneg this (by positivity)
      have hb : (0 : ℝ) ≤ 8 * α * z ^ 3 := by positivity
      have hc : (10 + 2 * α) * z ^ 2 ≤ 12 * z ^ 2 := by nlinarith [sq_nonneg z, hα1]
      have hd : 12 * z ^ 2 ≤ 16 * (1 + z) ^ 4 := by
        have hexp : 16 * (1 + z) ^ 4 - 12 * z ^ 2
            = 16 * z ^ 4 + 64 * z ^ 3 + 84 * z ^ 2 + 64 * z + 16 := by ring
        have : (0 : ℝ) ≤ 16 * z ^ 4 + 64 * z ^ 3 + 84 * z ^ 2 + 64 * z + 16 := by positivity
        linarith
      linarith
  rw [le_div_iff₀ hz, phiA_combined α z hz1, abs_div, abs_of_pos h4, div_mul_eq_mul_div,
    div_le_iff₀ h4]
  simpa [abs_mul, abs_of_pos hz] using hMz

end Work.FTS.PhiStar.Series

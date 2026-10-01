import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

namespace Work.OffAxis.Tf72One

/-- The imaginary-axis value of `G72` is `O(σ^{-4})`: for `σ ≥ 4`,
`(G72 (iσ)).re ≤ 10/σ^4`.  From `G72_re_closed_zero`,
`(G72 (iσ)).re = 4/σ⁴ + 4/σ⁶ + cos(2σ)(4σ²-4)/σ⁶ - 8sin(2σ)/σ⁵ ≤ 8/σ⁴ + 8/σ⁵ ≤ 10/σ⁴` (using `|cos|,|sin| ≤ 1`
and `σ ≥ 4`). -/
theorem C_le (σ : ℝ) (hσ : 4 ≤ σ) :
    (Work.ZeroFreeTables.G72 ((σ : ℂ) * Complex.I)).re ≤ 10 / σ ^ 4 := by
  have hσpos : 0 < σ := by linarith
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  rw [Work.ZeroFreeTables.OffAxis.G72_re_closed_zero hσne]
  have hc1 : Real.cos (2*σ) ≤ 1 := Real.cos_le_one _
  have hs2 : -1 ≤ Real.sin (2*σ) := Real.neg_one_le_sin _
  have h6pos : 0 < σ^6 := by positivity
  have hnum : 0 ≤ 4*(σ^2-1) := by nlinarith
  -- the `cos` term is at most `4(σ²-1)/σ⁶`
  have hc : Real.cos (2*σ)*(4*(σ^2-1)/σ^6) ≤ 4*(σ^2-1)/σ^6 := by
    have hcnn : 0 ≤ 4*(σ^2-1)/σ^6 := div_nonneg hnum (le_of_lt h6pos)
    have h := mul_le_mul_of_nonneg_right hc1 hcnn
    linarith
  -- the `sin` term is at most `8/σ⁵`
  have hs : Real.sin (2*σ)*(-(8/σ^5)) ≤ 8/σ^5 := by
    have hpos5 : (0:ℝ) < 8/σ^5 := by positivity
    have h := mul_le_mul_of_nonpos_right hs2 (by linarith : -(8/σ^5) ≤ 0)
    simpa using h
  have hA : 4/σ^4 + 4/σ^6 + Real.cos (2*σ)*(4*(σ^2-1)/σ^6) + Real.sin (2*σ)*(-(8/σ^5))
      ≤ 4/σ^4 + 4/σ^6 + (4*(σ^2-1)/σ^6) + 8/σ^5 := by
    exact add_le_add (add_le_add (add_le_add le_rfl le_rfl) hc) hs
  -- `4/σ⁴ + 4/σ⁶ + 4(σ²-1)/σ⁶ = 8/σ⁴`
  have hB : 4/σ^4 + 4/σ^6 + (4*(σ^2-1)/σ^6) + 8/σ^5 = 8/σ^4 + 8/σ^5 := by
    field_simp; ring
  -- `8/σ⁵ ≤ 2/σ⁴` since `σ ≥ 4`
  have hkey : 8/σ^5 ≤ 2/σ^4 := by
    have h2 : (2:ℝ)/σ^4 = (2*σ)/σ^5 := by field_simp
    rw [h2]
    exact div_le_div_of_nonneg_right (by linarith : (8:ℝ) ≤ 2*σ) (by positivity)
  have hsum : (8:ℝ)/σ^4 + 2/σ^4 = 10/σ^4 := by ring
  linarith [hA, hB, hkey, hsum]

end Work.OffAxis.Tf72One

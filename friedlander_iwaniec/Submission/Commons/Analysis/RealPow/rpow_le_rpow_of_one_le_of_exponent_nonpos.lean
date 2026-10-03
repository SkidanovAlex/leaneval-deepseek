import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.RealPow

theorem rpow_le_rpow_of_one_le_of_exponent_nonpos {x y e : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (he : e ≤ 0) : y ^ e ≤ x ^ e := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hne : 0 ≤ -e := neg_nonneg.mpr he
  have h1 : x ^ (-e) ≤ y ^ (-e) := Real.rpow_le_rpow hx0.le hxy hne
  have hpy : 0 < y ^ (-e) := Real.rpow_pos_of_pos hy0 _
  have hpx : 0 < x ^ (-e) := Real.rpow_pos_of_pos hx0 _
  have hy : y ^ e = (y ^ (-e))⁻¹ := by
    simpa using Real.rpow_neg hy0.le (-e)
  have hxg : x ^ e = (x ^ (-e))⁻¹ := by
    simpa using Real.rpow_neg hx0.le (-e)
  rw [hy, hxg]
  exact (inv_le_inv₀ hpy hpx).mpr h1

end Commons.Analysis.RealPow
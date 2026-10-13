import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.ConstructionInstance.A0_rpow_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

lemma one_sub_one_sub_rpow_le {β u : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) : 1 - (1 - u) ^ (3 * β) ≤ (3 * u) ^ β := by
  have h1u : 0 ≤ 1 - u := by linarith
  have hb0 : 0 ≤ (1 - u) ^ (3 : ℝ) := Real.rpow_nonneg h1u 3
  have hb1 : (1 - u) ^ (3 : ℝ) ≤ 1 := by
    have h := Real.rpow_le_rpow h1u (show 1 - u ≤ 1 by linarith) (show (0 : ℝ) ≤ 3 by norm_num)
    rwa [Real.one_rpow] at h
  have hbβ1 : ((1 - u) ^ (3 : ℝ)) ^ β ≤ 1 := by
    have h := Real.rpow_le_rpow hb0 hb1 hβ.le
    rwa [Real.one_rpow] at h
  have habs := A0_rpow_sub_le (β := β) (t := 1) (u := (1 - u) ^ (3 : ℝ)) hβ hβ1
      (by norm_num) hb0
  rw [Real.one_rpow,
      abs_of_nonneg (sub_nonneg.mpr hbβ1), abs_of_nonneg (sub_nonneg.mpr hb1)] at habs
  -- habs : 1 - ((1-u)^3)^β ≤ (1 - (1-u)^3)^β
  have hb3 : (1 - u) ^ (3 : ℝ) = (1 - u) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.rpow_mul h1u 3 β]
  refine le_trans habs ?_
  refine Real.rpow_le_rpow ?_ ?_ hβ.le
  · rw [hb3]
    have hfac : 1 - (1 - u) ^ (3 : ℕ) = u * (u ^ 2 - 3 * u + 3) := by ring
    rw [hfac]
    exact mul_nonneg hu0 (by nlinarith [sq_nonneg (2 * u - 3)])
  · rw [hb3]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) (show u - 3 ≤ 0 by linarith)]

end Work.ConstructionInstance

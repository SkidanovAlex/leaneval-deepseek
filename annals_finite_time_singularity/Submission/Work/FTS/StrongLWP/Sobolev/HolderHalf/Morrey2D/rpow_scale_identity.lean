import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

theorem rpow_scale_identity {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (t ^ 2)⁻¹ * (4 * (t * a) ^ 2) ^ (3 / 4 : ℝ) = (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) := by
  -- `(t ^ 2) ^ (3/4) = t ^ (3/2)` for `t > 0`
  have hA : (t ^ 2) ^ (3 / 4 : ℝ) = t ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast_mul (le_of_lt ht) 2 (3 / 4)]
    norm_num
  -- pull the factor `t ^ 2` out of the base `4 * (t * a) ^ 2 = (4 * a ^ 2) * t ^ 2`
  have hkey : (4 * (t * a) ^ 2) ^ (3 / 4 : ℝ) = (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (3 / 2 : ℝ) := by
    have hta : 4 * (t * a) ^ 2 = (4 * a ^ 2) * (t ^ 2) := by ring
    rw [hta, Real.mul_rpow (by positivity) (by positivity), hA]
  -- the remaining power bookkeeping: `(t ^ 2)⁻¹ * t ^ (3/2) = t ^ (-1/2)`
  have hc : (t ^ 2)⁻¹ * t ^ (3 / 2 : ℝ) = t ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_ofNat t 2, ← Real.rpow_neg (le_of_lt ht) 2, ← Real.rpow_add ht (-2) (3 / 2)]
    norm_num
  rw [hkey]
  calc (t ^ 2)⁻¹ * ((4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (3 / 2 : ℝ))
      = (4 * a ^ 2) ^ (3 / 4 : ℝ) * ((t ^ 2)⁻¹ * t ^ (3 / 2 : ℝ)) := by ring
    _ = (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) := by rw [hc]

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

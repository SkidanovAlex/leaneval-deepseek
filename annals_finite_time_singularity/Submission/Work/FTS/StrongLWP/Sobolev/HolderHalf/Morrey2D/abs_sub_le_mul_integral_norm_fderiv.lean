import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

theorem abs_sub_le_mul_integral_norm_fderiv {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p))
    (w z : ℝ × ℝ) :
    |v z - v w| ≤ ‖z - w‖ * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (w + t • (z - w))‖ := by
  -- `fderiv ℝ v` is continuous, since `v` is `C¹`
  have hfd := hv.continuous_fderiv (by norm_num)
  have hcont : Continuous fun t : ℝ => fderiv ℝ v (w + t • (z - w)) :=
    hfd.comp (continuous_const.add (continuous_id.smul continuous_const))
  -- rewrite the difference as the segment integral given by `hseg`
  rw [hseg w z, ← Real.norm_eq_abs]
  calc ‖∫ t in (0:ℝ)..1, (fderiv ℝ v (w + t • (z - w))) (z - w)‖
      ≤ ∫ t in (0:ℝ)..1, ‖z - w‖ * ‖fderiv ℝ v (w + t • (z - w))‖ := by
        -- the norm of the integral is at most the integral of the norms, and each
        -- integrand is bounded by `‖z - w‖` times the operator norm
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · filter_upwards with t ht
          have h := ContinuousLinearMap.le_opNorm (fderiv ℝ v (w + t • (z - w))) (z - w)
          rw [mul_comm] at h
          exact h
        · exact (hcont.norm.const_mul _).intervalIntegrable _ _
    _ = ‖z - w‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ v (w + t • (z - w))‖ :=
        intervalIntegral.integral_const_mul _ _

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

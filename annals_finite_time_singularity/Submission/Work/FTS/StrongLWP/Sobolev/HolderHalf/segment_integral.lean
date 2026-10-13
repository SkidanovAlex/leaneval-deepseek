import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

/-- Fundamental theorem of calculus along the segment from `p` to `z` in `ℝ × ℝ`:
for a `C¹` function `v`, the total increment equals the integral of the directional
derivative along the segment. -/
theorem segment_integral {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (p z : ℝ × ℝ) :
    v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p) := by
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => v (p + t • (z - p)))
        ((fderiv ℝ v (p + t • (z - p))) (z - p)) t := by
    intro t _
    have hcur : HasDerivAt (fun t : ℝ => p + t • (z - p)) (z - p) t := by
      have h1 := (hasDerivAt_id t).smul_const (z - p)
      have h2 := h1.const_add p
      simpa using h2
    exact (hd.differentiableAt.hasFDerivAt).comp_hasDerivAt t hcur
  have hint : IntervalIntegrable (fun t : ℝ => (fderiv ℝ v (p + t • (z - p))) (z - p))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hcont := hv.continuous_fderiv_apply (by norm_num)
    exact hcont.comp
      ((continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp

end Work.FTS.StrongLWP.Sobolev.HolderHalf

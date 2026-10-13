import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

-- `hB : 0 ≤ B` is part of the requested statement; the estimate below does not need it.
set_option linter.unusedVariables false

namespace Work.FTS.PhiStar.RadGreenSupport

/-- A function bounded on `(0, ∞)` is integrable against `t ^ (r - 1)` on `(0, z]` whenever
`r > 0`: the pure power `t ↦ t ^ (r - 1)` is integrable on `(0, z]` because its exponent exceeds
`-1`, and `f` is dominated by the constant `B ≥ 0` there. -/
theorem ioc_bounded_integrable {f : ℝ → ℝ} {r z B : ℝ} (hr : 0 < r) (hz : 0 < z)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Set.Ioi 0)) (hfb : ∀ t : ℝ, 0 < t → |f t| ≤ B) :
    MeasureTheory.IntegrableOn (fun t : ℝ => f t * t ^ (r - 1)) (Set.Ioc 0 z) := by
  -- the pure power is integrable on `(0, z]`, since `-1 < r - 1`
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (r - 1)) (Set.Ioc 0 z) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  -- so is the dominating function `B * t ^ (r - 1)` (`B ≥ 0`)
  have hg : MeasureTheory.Integrable (fun t : ℝ => B * t ^ (r - 1))
      (volume.restrict (Set.Ioc 0 z)) := hbase.const_mul B
  -- the product is a.e. strongly measurable: it is continuous on `(0, z]`
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => f t * t ^ (r - 1))
      (volume.restrict (Set.Ioc 0 z)) := by
    have hcont : ContinuousOn (fun t : ℝ => f t * t ^ (r - 1)) (Set.Ioc 0 z) :=
      (hf.mono Set.Ioc_subset_Ioi_self).mul
        (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1)))
    exact hcont.aestronglyMeasurable measurableSet_Ioc
  refine MeasureTheory.Integrable.mono' hg hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  exact mul_le_mul_of_nonneg_right (hfb t ht.1) (Real.rpow_nonneg ht.1.le _)

end Work.FTS.PhiStar.RadGreenSupport

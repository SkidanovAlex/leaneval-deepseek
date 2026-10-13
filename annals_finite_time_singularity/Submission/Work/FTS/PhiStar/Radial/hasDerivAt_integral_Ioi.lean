import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Radial

/-- Fundamental theorem of calculus for the tail integral: if `f` is continuous on `(a, ∞)` and
integrable there, then `u ↦ ∫ t in (u, ∞), f t` has derivative `-f z` at any `z > a`. -/
theorem hasDerivAt_integral_Ioi {f : ℝ → ℝ} {a z : ℝ} (haz : a < z)
    (hf : ContinuousOn f (Set.Ioi a)) (hint : MeasureTheory.IntegrableOn f (Set.Ioi a)) :
    HasDerivAt (fun u => ∫ t in Set.Ioi u, f t) (-(f z)) z := by
  have hz : z ∈ Set.Ioi a := haz
  -- `f` is continuous at `z`
  have hcont : ContinuousAt f z :=
    (hf.continuousWithinAt hz).continuousAt (isOpen_Ioi.mem_nhds hz)
  -- `f` is interval integrable on `[a, z]`
  have hII : IntervalIntegrable f MeasureTheory.volume a z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le haz.le]
    exact hint.mono_set Set.Ioc_subset_Ioi_self
  -- fundamental theorem of calculus for `u ↦ ∫ t in a..u, f t`
  have hFTC : HasDerivAt (fun u => ∫ t in a..u, f t) (f z) z :=
    intervalIntegral.integral_hasDerivAt_right hII
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hf z hz) hcont
  have hconst :
      HasDerivAt (fun u => (∫ t in Set.Ioi a, f t) - ∫ t in a..u, f t) (-(f z)) z := by
    simpa using hFTC.const_sub (∫ t in Set.Ioi a, f t)
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
  have hb : MeasureTheory.IntegrableOn f (Set.Ioi u) :=
    hint.mono_set (Set.Ioi_subset_Ioi hu.le)
  have hadd := intervalIntegral.integral_interval_add_Ioi (a := a) (b := u)
    (μ := MeasureTheory.volume) hint hb
  linarith

end Work.FTS.PhiStar.Radial

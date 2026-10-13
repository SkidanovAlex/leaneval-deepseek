import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.Clock

/-- **`t' = A`**: the physical time `t(τ) = ∫₀^τ A` is differentiable with derivative `A(τ)` in the
interior of the fake-time half-line.  This is the fundamental theorem of calculus for the upper
limit of an interval integral, `A` being continuous at `τ` by `PhysClock.hAcont` and `0 < τ`. -/
theorem hasDerivAt_t (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 < τ) : HasDerivAt C.t (C.A τ) τ := by
  -- `A` is interval-integrable on `[0,τ]` since it is continuous there
  have hci : IntervalIntegrable C.A MeasureTheory.volume 0 τ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hτ.le]
    exact C.hAcont.mono Set.Icc_subset_Ici_self
  -- `τ` lies in the interior of `[0,∞)`, so continuity on `[0,∞)` gives continuity at `τ`
  have hcont : ContinuousAt C.A τ :=
    (C.hAcont.continuousWithinAt (Set.mem_Ici.mpr hτ.le)).continuousAt
      (Filter.mem_of_superset (isOpen_Ioi.mem_nhds hτ) Set.Ioi_subset_Ici_self)
  have hsm : StronglyMeasurableAtFilter C.A (nhds τ) MeasureTheory.volume :=
    C.hAcont.mono Set.Ioi_subset_Ici_self |>.stronglyMeasurableAtFilter isOpen_Ioi τ
      (Set.mem_Ioi.mpr hτ)
  exact intervalIntegral.integral_hasDerivAt_right hci hsm hcont

end Work.FTS.Physical.Clock

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-- A pointwise limit, on the open interval `(0, π/2)`, of functions continuous there is
almost everywhere measurable for the measure `volume` restricted to `Iθ = [0, π/2]`.

The endpoints `0` and `π/2` are null for `volume`, so the restricted measures on the open
and the closed interval coincide, and on the open interval the limit of measurable
functions is measurable. -/
theorem aemeasurable_slice_of_tendsto_Ioo {un : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hcont : ∀ n : ℕ, ContinuousOn (un n) (Set.Ioo (0 : ℝ) (π / 2)))
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Filter.Tendsto (fun n => un n θ) Filter.atTop (nhds (u θ))) :
    AEMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hs : MeasurableSet (Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo.measurableSet
  -- On the open interval the limit is a.e. measurable.
  have h1 : AEMeasurable u (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    refine aemeasurable_of_tendsto_metrizable_ae' (fun n => (hcont n).aemeasurable hs) ?_
    filter_upwards [ae_restrict_mem hs] with θ hθ
    exact hconv θ hθ
  -- The open and closed intervals differ by the null set `{0, π/2}`.
  rw [Work.Spaces.Iθ, ← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  exact h1

end Work.FTS_EllLimOK

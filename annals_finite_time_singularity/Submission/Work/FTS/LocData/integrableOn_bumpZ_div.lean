/-
# `Work.FTS.LocData.integrableOn_bumpZ_div` — `bumpZ s / s` is integrable on `(0,∞)`

The radial bump `bumpZ z = χ(4z - 5)` is smooth with support contained in the closed interval
`[3/4, 7/4]` (`Work.FTS.LocData.BumpZ_contDiff`, `Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc`),
so on the half line `Ioi 0` the function `s ↦ bumpZ s / s` is bounded, supported on the compact
interval `[3/4, 7/4]`, and coincides there with a continuous function (the denominator `s` is
bounded away from `0` on that interval, where `s ≥ 3/4`).  Hence it is integrable on `Ioi 0`.

The proof is the standard compact-support argument:

* `s ↦ bumpZ s / s` is continuous on the compact `K = [3/4, 7/4]`, hence `IntegrableOn` there
  (`ContinuousOn.integrableOn_compact`);
* the indicator `K.indicator (bumpZ · / ·)` is therefore integrable for `volume`
  (`MeasureTheory.integrable_indicator_iff`), hence also on `Ioi 0`
  (`MeasureTheory.Integrable.integrableOn`);
* on `Ioi 0` that indicator agrees pointwise with `bumpZ · / ·`, because `bumpZ` vanishes off `K`
  (`MeasureTheory.IntegrableOn.congr_fun`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.BumpZ_contDiff
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

theorem integrableOn_bumpZ_div :
    MeasureTheory.IntegrableOn (fun s : ℝ => Work.FTS.LocData.bumpZ s / s) (Set.Ioi (0 : ℝ)) := by
  -- The function is continuous on the compact support interval.
  have hK : MeasureTheory.IntegrableOn (fun s : ℝ => Work.FTS.LocData.bumpZ s / s)
      (Set.Icc (3 / 4 : ℝ) (7 / 4)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine (BumpZ_contDiff.continuous.continuousOn).div continuous_id.continuousOn ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
    exact ne_of_gt hx0
  have hmeas : MeasurableSet (Set.Icc (3 / 4 : ℝ) (7 / 4)) := measurableSet_Icc
  -- Its indicator is integrable for `volume` (compact support), hence on `Ioi 0`.
  have hind : MeasureTheory.Integrable
      ((Set.Icc (3 / 4 : ℝ) (7 / 4)).indicator
        (fun s : ℝ => Work.FTS.LocData.bumpZ s / s)) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hmeas).mpr hK
  have h2 : MeasureTheory.IntegrableOn
      ((Set.Icc (3 / 4 : ℝ) (7 / 4)).indicator
        (fun s : ℝ => Work.FTS.LocData.bumpZ s / s)) (Set.Ioi (0 : ℝ)) :=
    hind.integrableOn
  -- On `Ioi 0` the indicator agrees with the function itself, since `bumpZ` vanishes off `K`.
  refine MeasureTheory.IntegrableOn.congr_fun h2 (fun x _ => ?_) measurableSet_Ioi
  by_cases hxK : x ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · rw [Set.indicator_of_mem hxK]
  · rw [Set.indicator_of_notMem hxK, bumpZ_eq_zero_of_notMem_Icc x hxK, zero_div]

end Work.FTS.LocData

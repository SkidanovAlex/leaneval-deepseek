import Mathlib
import Submission.Work.OddVolterra.WinData.LowClamp
import Submission.Work.OddVolterra.WinData.manifest_locality_low
import Submission.Work.OddVolterra.WinData.frozen_tail_close_low
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddExistence.Estimates.theta_lipschitz

/-!
# The source of the low-slope piece

The low-slope system on `[1/4, 4/5]` has *fixed* data (`lcGodd`, `lcTheta`) and the only
`h`-dependence sits in the source: the paper's `Xi n h` plus the part of the `σ`-integral that
runs over the region where the solution is already known (the middle piece `Z`).

This file defines the two sources (`lcXi`, `lcXi₀`).
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-- The source of the low-slope piece: the paper's `Xi n h` plus the `σ`-integral from `4/5` to
`1`, evaluated on the already constructed middle piece `Z` (which equals `baseState` past
`9/10`). -/
def lcXi (n : ℕ) (h : ℝ → ℝ) (Z : ℝ → St) (s : ℝ) : St :=
  Xi n h s + (∫ σ in (4 / 5 : ℝ)..(19 / 20 : ℝ), Theta n h s σ (Z σ)) +
    (∫ σ in (19 / 20 : ℝ)..(1 : ℝ), Theta n h s σ (baseState σ))

/-- The unperturbed source of the low-slope piece: the source for which `baseState` solves the
low-slope system with right endpoint `4/5`. -/
def lcXi₀ (n : ℕ) (s : ℝ) : St :=
  Xi n 0 s + (∫ σ in (4 / 5 : ℝ)..(1 : ℝ), Theta n 0 s σ (baseState σ))

end

end Work.OddVolterra.WinData

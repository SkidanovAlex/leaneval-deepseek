import Mathlib
import Submission.Work.EQ.FanTri.Base
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanSep.centre_numbers
import Submission.Work.EQ.FanSep.step_w
import Submission.Work.EQ.FanSep.step_x
import Submission.Work.EQ.FanSep.germ_lip

/-!
# Definitions for the quantitative fan decay (`Work.EQ.FanTri.fan_decay`)

`Vis ε` is the number of *levels* `1 ≤ i ≤ |ε|` of the word `ε` whose walk state is nonzero,
i.e. the number of visits of the fan walk to a centre other than `A₁` counted on the levels
strictly inside the level `0`.  This is the exponent that the decay estimate of
`fan_decay` carries.

`tau a ε` is the per-step gain `λ·|c - a/2|/|c + a/2|` at the level-0 centre of `ε`: it equals
`1` at `A₁` and is at most `fanTh a` otherwise.
-/

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

/-- Levels `1 ≤ i ≤ |ε|` whose walk state is nonzero, indexed by `i = j + 1` with `j ∈ range |ε|`.
This is the "correct" exponent of the quantitative fan decay: it counts the visits to a centre
other than `A₁` and is one less than `fVis ε` exactly when the level-`0` centre is `A₁`. -/
def Vis (ε : List Bool) : ℕ :=
  ((Finset.range ε.length).filter (fun j => fLvl ε (j + 1) ≠ 0)).card

/-- The one-step gain factor at a word whose level-`0` state is `fLvl ε 0`. -/
noncomputable def tau (a : ℝ) (ε : List Bool) : ℝ := if fLvl ε 0 = 0 then 1 else fanTh a

/-- The induction invariant of the quantitative fan decay: analyticity, the abscissa
deviation (`ϑ^{Vis ε}`), the semi-projective coordinate, nonvanishing of `x - a/2` and
positivity of the real part of the radicand `(x + a/2)² + y²`. -/
def FanDecay (a : ℝ) (h : ℂ → ℂ) (Ke Lam Q : ℝ) (ε : List Bool) (v : ℂ) : Prop :=
  AnalyticAt ℂ (fan a h ε) v ∧
    ‖(fan a h ε v).1 - (fan a h ε 0).1‖ ≤ Ke * (fanTh a) ^ (Vis ε) * ‖v‖ ∧
    ‖(fan a h ε v).2 / ((fan a h ε v).1 - ((a / 2 : ℝ) : ℂ))‖
        ≤ Lam * (fanTh a) ^ (Vis ε) * ‖v‖ * (1 + Q * ‖v‖) ∧
    (fan a h ε v).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 ∧
    0 < (((fan a h ε v).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (fan a h ε v).2 ^ 2).re

end

end Work.EQ.FanTri

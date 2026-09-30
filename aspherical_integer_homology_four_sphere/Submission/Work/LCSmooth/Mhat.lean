/-
# Area `LCSmooth`: the `cov_smooth` field of `Work.Final.FinalInputs`, at `M̂`

This file is the **deliverable** of the area: the field

    cov_smooth : CovariantDerivative.ContMDiffCovariantDerivative (mhatCov (rt := rt)) ∞

of the class `Work.Final.FinalInputs` (`Submission/Work/Final/Basic.lean`), where `M̂ = rt.Mhat` is
the assembled Ratcliffe–Tschantz space of the area `Space` and
`Work.Final.mhatCov (rt := rt) = Work.LeviCivita.lcConn (I := I4) (M := rt.Mhat)`.

Both spellings of the grade are given (`Work.LCSmooth.smoothGrade`, which is
`((⊤ : ℕ∞) : WithTop ℕ∞)`, and the `∞` of the `ContDiff` notation for `ℕ∞ω`; they are
definitionally equal, `Work.LCSmooth.smoothGrade_eq_final`, `smoothGrade_eq_infty`), and the
statement is registered as a *global instance*, so that

* `cov_smooth := inferInstance` in a `Work.Final.FinalInputs` literal,
* the extra instance argument of `Work.Final.curvLe_of_models` (`… : RauchK.CurvLe (mhatCov) K`),
* the extra argument of `Work.Final.FinalInputs.curvLe_field`,
* and the instance arguments of the Cartan–Hadamard chain
  (`Work.CartanHadamard.curvLe_all`, `aspherical_of_curvLe`, …)

are all discharged by typeclass inference, with no hypothesis to thread by hand.

The mathematical content is the theorem `Work.LCSmooth.lcConn_contMDiff` of
`Submission/Work/LCSmooth/Defs.lean` (proved in the area `LeviCivita` by computing the connection
in charts from the Koszul formula: see `Submission/Work/LeviCivita/NOTES.md` §5).
-/
import Submission.Work.LCSmooth.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open CategoryTheory

namespace Work.LCSmooth

noncomputable section

section Mhat

variable [rt : Work.Space.RTData]

/-- **The `cov_smooth` field of `Work.Final.FinalInputs`** (instance form): the Levi-Civita
connection of the assembled space `M̂` is a smooth covariant derivative.

The instance is registered globally, so that a `Work.Final.FinalInputs` literal can fill the field
with `cov_smooth := inferInstance` as soon as this module is imported. -/
instance instContMDiffCovariantDerivativeMhatCov :
    CovariantDerivative.ContMDiffCovariantDerivative
      (Work.Final.mhatCov (rt := rt)) Work.Final.smoothGrade :=
  Work.LCSmooth.lcConn_contMDiff (I := Work.Space.I4) (M := rt.Mhat)

/-- **The `cov_smooth` field of `Work.Final.FinalInputs`**, with the grade written as
`Work.Final.smoothGrade` (the spelling of `Submission/Work/Final/Framework.lean`). -/
theorem mhatCov_contMDiff :
    CovariantDerivative.ContMDiffCovariantDerivative
      (Work.Final.mhatCov (rt := rt)) Work.Final.smoothGrade :=
  inferInstance

/-- **The `cov_smooth` field of `Work.Final.FinalInputs`**, with the grade written as
`Work.LCSmooth.smoothGrade` (definitionally the previous one). -/
theorem cov_smooth :
    CovariantDerivative.ContMDiffCovariantDerivative
      (Work.Final.mhatCov (rt := rt)) Work.LCSmooth.smoothGrade :=
  inferInstance

/-- **The `cov_smooth` field of `Work.Final.FinalInputs`**, in the spelling of the class
declaration itself (`∞`, i.e. the `∞` of the `ContDiff` notation, which in
`Submission/Work/Final/Basic.lean` is elaborated with the `ENNReal` scope open).

The three statements `mhatCov_contMDiff`, `cov_smooth`, `cov_smooth_infty` are *the same
proposition*, up to definitional equality of the grade; all three are provided so that a caller
never has to worry about which spelling they used. -/
theorem cov_smooth_infty :
    CovariantDerivative.ContMDiffCovariantDerivative
      (Work.Final.mhatCov (rt := rt)) (∞ : ℕ∞ω) :=
  inferInstance

/-- The bundled connection of `M̂`: the Levi-Civita connection as a `Work.Final.ChartedRiemConn`
(smooth, compatible with the metric, torsion free). -/
noncomputable def mhatChartedRiemConn : Work.Final.ChartedRiemConn rt.Mhat :=
  Work.LCSmooth.chartedRiemConn (M := rt.Mhat)

/-- The bundled connection of `M̂`, as an instance. -/
instance instChartedRiemConnMhat : Work.Final.ChartedRiemConn rt.Mhat :=
  mhatChartedRiemConn

theorem mhatChartedRiemConn_cov :
    (mhatChartedRiemConn (rt := rt)).cov = Work.Final.mhatCov (rt := rt) := rfl

end Mhat

section Consumer

example [rt : Work.Space.RTData] :
    CovariantDerivative.ContMDiffCovariantDerivative
      (Work.Final.mhatCov (rt := rt)) Work.Final.smoothGrade := inferInstance

example [rt : Work.Space.RTData] :
    CovariantDerivative.ContMDiffCovariantDerivative
      (Work.Final.mhatCov (rt := rt)) (∞ : ℕ∞ω) := inferInstance

example [rt : Work.Space.RTData] : Work.Final.ChartedRiemConn rt.Mhat := inferInstance

example [rt : Work.Space.RTData] : Work.Final.ChartedRiem rt.Mhat := inferInstance

end Consumer

end

end Work.LCSmooth

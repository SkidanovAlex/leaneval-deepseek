import Submission.Work.ANALYTIC.Main
import Submission.Work.ANALYTIC.boundedSeqIncl_solidEquiv

/-!
# Unconditional forms of the area's results

Area FLAT proves `FlatProp` (`Work.FLAT.flat_prop`), so the conditionals of this area can be
discharged.  This module collects the unconditional forms; it is separate from `Main.lean` only
because `boundedSeqIncl_solidEquiv` (AN2) uses `Main.solidNull_of_realModule'`, so importing it from
`Main` would create a cycle.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **AN2**: the inclusion `∏^bnd ℤ ⟶ ∏ℤ` is a solid-equivalence (unconditional; `ToolkitProp` is
proved in area TOOLKIT and `FlatProp` in area FLAT). -/
theorem solidEquiv_boundedSeqIncl (hTK : Submission.Blueprint.ToolkitProp) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map boundedSeqIncl) :=
  haveI : PreservesFiniteLimits (tensorLeft P) := flat_P_unconditional
  boundedSeqIncl_solidEquiv flatProp hTK

end Work.ANALYTIC

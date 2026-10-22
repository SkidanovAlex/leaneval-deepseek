import Submission.Work.ANALYTIC.Unconditional
import Submission.Work.ANALYTIC.MuT

/-!
# The area's results with all cross-area inputs discharged

Areas FLAT (`Work.FLAT.flat_prop`) and TOOLKIT (`Work.TOOLKIT.toolkit_prop`) supply `FlatProp` and
`ToolkitProp`, so the conditionals of this area become unconditional here.  (This module is
separate from `Unconditional.lean` because `MuT` and `exists_muT` already use `Unconditional`.)
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **AN2, unconditional.** -/
theorem solidEquiv_boundedSeqIncl' :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map boundedSeqIncl) :=
  solidEquiv_boundedSeqIncl toolkitProp

/-- **AN1 + AN2 composed**: `P ⟶ ∏^bnd ℤ ⟶ ∏ℤ` is a solid-equivalence. -/
theorem solidEquiv_cBoundedIncl :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (cBounded ≫ boundedSeqIncl)) := by
  simpa only [Functor.map_comp] using
    toolkitProp.comp _ _ solidEquiv_cBounded' solidEquiv_boundedSeqIncl'

end Work.ANALYTIC

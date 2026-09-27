import Mathlib
import Submission.Work.Mostow.HLDefsRe
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.ftbUnfold

namespace Work.Mostow

theorem measurableSetNearIdAt {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (b : LeanEval.Geometry.MostowRigidity.PO n 1) (η : ℝ) :
    MeasurableSet {u : Submission.Mostow.E n | Submission.Mostow.NearIdAt b u η} :=
  ftbMeasurableSetNearId n hA hI b η

end Work.Mostow

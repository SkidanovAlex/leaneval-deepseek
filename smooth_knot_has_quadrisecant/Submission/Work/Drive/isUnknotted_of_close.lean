import Mathlib
import Submission.Work.Drive.circleBandArc
import Submission.Work.Drive.closeAux

namespace Work.Drive

/-- C¹-close analytic knots are unknotted simultaneously: correcting the whole isotopy by `(1-s) • (r - r')` keeps every slice a knot (the correction is uniformly C¹-small and the slices of the given isotopy have uniform positive injectivity margins over the compact slab). -/
theorem isUnknotted_of_close {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' →
      (∀ t : ℝ, ‖r' t - r t‖ < ε ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε) →
      LeanEval.KnotTheory.Quadrisecant.IsUnknotted r' →
      LeanEval.KnotTheory.Quadrisecant.IsUnknotted r := by
  exact closeAux hr

end Work.Drive

import Mathlib
import Submission.Work.Drive.projRot

namespace Work.Drive

/-- **The projection `cappingSpaceHomeoProj` intertwines `rotCapping` with `projRot`.**  In the model
`CappingSpace ≃ₜ (0,∞) × ℝP³` of `exists_cappingModel_projectivization` the rotation acts on the
`ℝP³` factor only, by `projRot`, the radial coordinate being untouched.  Concretely,
`cappingSpaceHomeoProj = cappingSpaceHomeoSlice.trans (refl.prodCongr lensSpaceHomeoProj)` with
`cappingSpaceHomeoSlice x = Φ x`, so both sides are the pair with first coordinate `(Φ p).1` and second
coordinate `projRot t (lensToProj ((Φ p).2))`; the rewriting lemmas are the equivariance
`Phi_rot_equivariant` of the slice rotation and `lensToProj_rotLens`. -/
theorem cappingSpaceHomeoProj_rotCapping (t : ℝ) (p : Work.Drive.CappingSpace) :
    Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.rotCapping ((t : ℝ) : UnitAddCircle) p)
      = ((Work.Drive.cappingSpaceHomeoProj p).1,
         Work.Drive.projRot t ((Work.Drive.cappingSpaceHomeoProj p).2)) := by
  refine Prod.ext ?_ ?_
  · show (Φ (rotCapping ((t : ℝ) : UnitAddCircle) p)).1 = (Φ p).1
    rw [(Phi_rot_equivariant _).1 p]
  · show lensToProj ((Φ (rotCapping ((t : ℝ) : UnitAddCircle) p)).2)
      = projRot t (lensToProj ((Φ p).2))
    rw [(Phi_rot_equivariant _).1 p, lensToProj_rotLens]

end Work.Drive

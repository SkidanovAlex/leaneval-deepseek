import Mathlib
import Submission.Work.Drive.diskLiftHomotopy

namespace Work.Drive

/-- **The lift of the rotated chart.**  If `V` is a nonvanishing vector lift of the class map of the
disk chart `Q`, then `diagRotL t ∘ V` is a nonvanishing lift of the class map of the rotated chart
`fun z => rotCapping t (Q z)` — the lift of the design's plane `P k = rotPresentation Q (u k)`.
The oddness on the boundary circle is preserved (`diagRotL _` is linear, so `map_neg`). -/
theorem isClassLift_rotCapping {Q : ℂ → CappingSpace} {V : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hV : ∀ z, V z ≠ 0) (h : Work.Drive.IsClassLift Q V hV) (t : ℝ) :
    ∃ (hW : ∀ z, Work.Drive.diagRotL t (V z) ≠ 0),
      Work.Drive.IsClassLift
        (fun z : ℂ => Work.Drive.rotCapping ((t : ℝ) : UnitAddCircle) (Q z))
        (fun z : ℂ => Work.Drive.diagRotL t (V z)) hW := by
  have hW' : ∀ z, Work.Drive.diagRotL t (V z) ≠ 0 :=
    fun z hz => hV z ((Work.Drive.diagRotL t).map_eq_zero_iff.mp hz)
  refine ⟨hW', fun z => ?_⟩
  rw [Work.Drive.cappingSpaceHomeoProj_rotCapping, h z, Work.Drive.projRot_mk]
  simp only [Work.Drive.diagRotL_apply]

end Work.Drive

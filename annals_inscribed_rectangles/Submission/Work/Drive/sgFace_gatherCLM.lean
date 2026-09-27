import Mathlib
import Submission.Work.Drive.sgPiecesDefs

namespace Work.Drive

noncomputable section

/-- **Reconstruction of a boundary point from its free coordinates.**  The eight face embeddings
`Work.Drive.sgFace k vv : ℝ³ → ℝ⁵` (one per box coordinate `k` and value `vv`) pin the `k`-th *box*
coordinate of `Amb 4 = ℝ⁵` at `vv` and the dummy coordinate `1` at `0`; `Work.Drive.gatherCLM k`
reads off the three free coordinates.  The content here: a point of the box whose dummy coordinate
vanishes is reconstructed by the face embedding of any of its box coordinates. -/
theorem sgFace_gatherCLM (k : Fin 4) (t : Fin 2) {z : Work.Drive.Amb 4}
    (hdummy : z 1 = 0) (ht : (t : ℝ) = z (Work.Drive.boxIdx k)) :
    Work.Drive.sgFace k t (Work.Drive.gatherCLM k z) = z := by
  -- `Amb 4 = ℝ⁵` is a `PiLp`, so it suffices to compare all five coordinates.
  apply PiLp.ext
  intro i
  -- the five coordinates of the box: the four `boxIdx k` and the dummy `1`
  fin_cases k <;> fin_cases i <;>
    simp +decide [sgFace, scatterCLM, basisVec5, coord3, boxIdx, ht, hdummy, Fin.sum_univ_three,
      PiLp.proj_apply] <;> rfl

end

end Work.Drive

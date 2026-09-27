import Mathlib
import Submission.Work.Drive.sgPiecesDefs

namespace Work.Drive

/-- **The free coordinates of a point of the box lie in the box.**  If every box coordinate of
`z : Amb 4 = ℝ⁵` (i.e. every coordinate other than the dummy `1`) lies in `[0,1]`, then the three free
coordinates read off by `Work.Drive.gatherCLM k` lie in the unit box of `ℝ³`. -/
theorem gatherCLM_mem_unitBox {k : Fin 4} {z : Work.Drive.Amb 4}
    (hbox : ∀ i : Fin 5, i ≠ 1 → z i ∈ Set.Icc (0 : ℝ) 1) :
    Work.Drive.gatherCLM k z ∈ Submission.Drive.unitBox 2 := by
  intro j
  rw [gatherCLM_apply]
  exact hbox _ (boxIdx_ne_dummy _)

end Work.Drive

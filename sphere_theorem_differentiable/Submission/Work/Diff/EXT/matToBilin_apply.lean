import Mathlib
import Submission.Work.Diff.EXT.glueDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

theorem matToBilin_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (A : Work.Diff.EXT.MatE (E := E)) (u v : E) :
    Work.Diff.EXT.matToBilin A u v
      = ∑ i, ∑ j, A i j * (Work.Diff.EXT.bB (E := E)).coord i u
          * (Work.Diff.EXT.bB (E := E)).coord j v := by
  rw [show Work.Diff.EXT.matToBilin A = Work.Diff.EXT.matToBilinLin A from rfl]
  simp only [Work.Diff.EXT.matToBilinLin, Work.Diff.EXT.matEntryCLM,
    LinearMap.sum_apply, Work.Diff.EXT.bilinElem, Work.Diff.EXT.bCoordCLM]
  simp [ContinuousLinearMap.smulRight_apply, mul_assoc]

end Work.Diff.EXT

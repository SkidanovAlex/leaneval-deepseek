import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-- The determinant of `imatOfList l` is the Sarrus-rule determinant `det9 l`. -/
theorem det9_spec (l : List ℤ) : (imatOfList l).det = det9 l := by
  rw [Matrix.det_fin_three]
  simp only [imatOfList, Matrix.of_apply, det9, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

end Work.SG

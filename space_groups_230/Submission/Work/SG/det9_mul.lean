import Mathlib
import Submission.Work.SG.SGprelude
import Submission.Work.SG.det9_spec

namespace Work.SG

/-- `det9` is multiplicative on flat matrices of length 9. -/
theorem det9_mul {a b : List ℤ} (ha : a.length = 9) (hb : b.length = 9) :
    det9 (m9mul a b) = det9 a * det9 b := by
  rw [← det9_spec, imatOfList_mul, Matrix.det_mul, det9_spec, det9_spec]

end Work.SG

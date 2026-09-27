import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Seg

lemma seg_eq_zero {a b u : ℝ} (hab : a < b) (hu : b ≤ |u|) : seg a b u = 0 := by
  have hba : 0 < b - a := by linarith
  have hnum : b - |u| ≤ 0 := by linarith
  have hquot : (b - |u|) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hba.le
  rw [seg, clamp, min_eq_right (by linarith : (b - |u|) / (b - a) ≤ (1 : ℝ)),
    max_eq_left hquot]

end Work.PL.Approx.Seg

import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Seg

lemma seg_eq_one {a b u : ℝ} (hab : a < b) (hu : |u| ≤ a) : seg a b u = 1 := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hquot : 1 ≤ (b - |u|) / (b - a) := by
    rw [le_div_iff₀ hba]
    linarith
  unfold seg clamp
  rw [min_eq_left hquot, max_eq_right zero_le_one]

end Work.PL.Approx.Seg

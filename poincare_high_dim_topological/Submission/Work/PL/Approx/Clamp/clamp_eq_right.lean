import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Clamp

lemma clamp_eq_right {a b x : ℝ} (hab : a ≤ b) (hb : b ≤ x) : clamp a b x = b := by
  simp only [clamp, min_eq_left hb, max_eq_right hab]

end Work.PL.Approx.Clamp

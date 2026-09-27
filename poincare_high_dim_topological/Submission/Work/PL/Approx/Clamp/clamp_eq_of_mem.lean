import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Clamp

lemma clamp_eq_of_mem {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) : clamp a b x = x := by
  unfold clamp
  rw [min_eq_right hb, max_eq_right ha]

end Work.PL.Approx.Clamp

import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Clamp

lemma continuous_clamp (a b : ℝ) : Continuous (fun x : ℝ => clamp a b x) := by
  unfold clamp
  fun_prop

end Work.PL.Approx.Clamp

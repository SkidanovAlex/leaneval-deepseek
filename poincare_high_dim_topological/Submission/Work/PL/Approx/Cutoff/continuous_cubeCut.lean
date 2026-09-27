import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Cutoff

open scoped BigOperators

lemma continuous_cubeCut {n : ℕ} (a b : ℝ) : Continuous (fun x : PL.E n => cubeCut a b x) := by
  unfold cubeCut seg clamp
  fun_prop

end Work.PL.Approx.Cutoff

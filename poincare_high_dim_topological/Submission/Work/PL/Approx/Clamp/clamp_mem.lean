import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Clamp

/-- `clamp a b x` lies in the interval `[a,b]` whenever that interval is nonempty. -/
lemma clamp_mem {a b x : ℝ} (hab : a ≤ b) : a ≤ clamp a b x ∧ clamp a b x ≤ b := by
  refine ⟨?_, ?_⟩
  · exact le_max_left a (min b x)
  · exact max_le hab (min_le_left b x)

end Work.PL.Approx.Clamp

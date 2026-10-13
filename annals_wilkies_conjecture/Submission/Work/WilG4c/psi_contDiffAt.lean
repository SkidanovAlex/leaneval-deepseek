import Mathlib
import Submission.Work.WilG4c.hbdd_defs

namespace Work.WilG4c

/-- `ψ(u) = 1/2 + u/(2√(1+u²))` is `C^1` (indeed smooth) everywhere. -/
theorem psi_contDiffAt (w : ℝ) : ContDiffAt ℝ 1 Work.WilkG4c.psi w := by
  unfold Work.WilkG4c.psi
  fun_prop (disch := positivity)

end Work.WilG4c

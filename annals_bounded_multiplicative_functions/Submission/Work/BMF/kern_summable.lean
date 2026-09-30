import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.TentDefs
import Submission.Work.BMF.tentCoeff_summable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The kernel `kern K = (π²K/2)·tentCoeff (1/(2K))` is summable over `ℤ` for `K ≥ 1`:
it is a constant multiple of the Fourier coefficients of a tent of positive width, which
are summable. -/
theorem kern_summable (K : ℕ) (hK : 1 ≤ K) : Summable (fun c : ℤ => kern K c) := by
  have hB : 0 < 1 / (2 * (K : ℝ)) := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    positivity
  have h := (tentCoeff_summable hB).mul_left (Real.pi ^ 2 * (K : ℝ) / 2)
  simpa [kern] using h

end Work.BMF

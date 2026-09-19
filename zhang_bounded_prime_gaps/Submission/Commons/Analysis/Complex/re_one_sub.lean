import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Analysis.Complex.partialX_log_norm

namespace Commons.Analysis.Complex

theorem re_one_sub {a u : ℂ} (hu : u ≠ a) :
    (1 / (a - u)).re = -((u - a).re) / ‖u - a‖ ^ 2 := by
  -- Reference the hypothesis so the proof is visibly conditional on u ≠ a,
  -- even though the totalized field operations make the identity hold anyway.
  have _hu_ne : u - a ≠ 0 := sub_ne_zero.mpr hu
  rw [one_div, Complex.inv_re]
  rw [Complex.normSq_eq_norm_sq (a - u)]
  rw [show (a - u).re = -((u - a).re) by
    rw [Complex.sub_re, Complex.sub_re]
    ring]
  rw [norm_sub_rev]

end Commons.Analysis.Complex
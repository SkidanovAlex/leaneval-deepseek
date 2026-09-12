import Mathlib
import Submission.S6Core

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex
set_option autoImplicit false

namespace Submission
namespace NumBounds

/-! Total upper-bound arithmetic for the assembled polynomial:

   `1 + 2·√q + 2·(9 + 2^12)·√q ≤ 2^14·√q` for `q ≥ 1`.

   Since `9 + 2^12 = 4105`, `2·(9 + 2^12) + 2 = 8212 ≤ 2^14 = 16384`, and
   `1 ≤ (2^14 − 8212)·√q = 8172·√q` once `√q ≥ 1` (i.e. `1 ≤ (q:ℝ)`).
   Straightforward `nlinarith`/`norm_num` with `Real.sqrt_nonneg`. -/

theorem upper_bound_total {q : ℕ} (hq : 1 ≤ (q : ℝ)) :
    1 + 2 * Real.sqrt (q : ℝ) + 2 * (9 + 2 ^ 12) * Real.sqrt (q : ℝ) ≤
      (2 ^ 14 : ℝ) * Real.sqrt (q : ℝ) := by
  have hsq : 1 ≤ Real.sqrt (q : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hq
  have hqnonneg : 0 ≤ (q : ℝ) := by positivity
  nlinarith [hsq]

end NumBounds
end Submission

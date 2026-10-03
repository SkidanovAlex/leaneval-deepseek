import Mathlib
import Submission.Commons.Analysis.ExpLog.case_B_arith

set_option autoImplicit false

namespace Commons.Analysis.Real

/-- For `c > 0` and `x ≥ 0`, `x ^ a * exp (-(c * x)) ≤ (a / (c * e)) ^ a`. -/
lemma pow_mul_exp_neg_le (a : ℕ) {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) :
    x ^ a * Real.exp (-(c * x)) ≤ ((a : ℝ) / (c * Real.exp 1)) ^ a :=
  Commons.Analysis.ExpLog.caseB_pow_mul_exp_neg_le a hc hx

end Commons.Analysis.Real

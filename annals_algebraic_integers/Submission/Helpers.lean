import ChallengeDeps

open AlgebraicIntegers
open ComplexOrder

set_option autoImplicit false

namespace Submission.Helpers

/-!
Verified helper infrastructure for the algebraic-integers problem.

* `Submission.Reduction.lambda_SSS_le_of_family` (in `Submission.Reduction`):
  an injective family of totally positive algebraic integers with
  `trace < c * degree` for all members implies `lambda_SSS ≤ c`.

The final step of the main theorem: `lambda_SSS ≤ c` with `c < 1.89831`
gives `lambda_SSS < 1.89831`.
-/

theorem lambda_SSS_lt_of_le {c : ℝ} (hc : c < 1.89831) (h : lambda_SSS ≤ c) :
    lambda_SSS < 1.89831 := lt_of_le_of_lt h hc

end Submission.Helpers

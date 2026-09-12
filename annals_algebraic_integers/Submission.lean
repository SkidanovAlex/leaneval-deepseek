import ChallengeDeps
import Submission.Helpers
import Submission.Reduction
import Submission.Explicit
import Submission.CloseTheorem

open AlgebraicIntegers
open ComplexOrder

set_option autoImplicit false

namespace Submission

theorem theorem_1_1 : lambda_SSS < 1.89831 := by
  exact Submission.CloseTheorem.theorem_1_1_of_contracts

end Submission

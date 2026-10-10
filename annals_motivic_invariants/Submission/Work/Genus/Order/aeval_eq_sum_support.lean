import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

theorem aeval_eq_sum_support {F : Type*} [Field F] (A : Polynomial F) (x : RatFunc F) :
    Polynomial.aeval x A = ∑ i ∈ A.support, algebraMap F (RatFunc F) (A.coeff i) * x ^ i := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]

end Work.Genus.Order

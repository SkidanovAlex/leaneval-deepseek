import ChallengeDeps
import Submission.Final

open UnitConjecture

set_option autoImplicit false

namespace Submission

theorem theorem_A : (∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1) ∧ IsUnit u ∧ ¬ ∃ g : P, u = g := by
  exact theorem_A_combined

end Submission

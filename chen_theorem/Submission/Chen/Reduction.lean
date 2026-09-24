import Mathlib
import ChallengeDeps
import Submission.Commons.Analysis.Asymptotics.unbounded_of_eventually_ge_mul_div_log_sq
import Submission.Chen.Interface

open LeanEval.NumberTheory.ChenTheorem
open Filter
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Submission

/-- A positive-rate lower bound `≥ c * x / (log x)^2` for the counting function
`chenCount` forces the challenge set to be infinite.  This is the interface that
Chen's weighted-sieve estimate plugs into. -/
theorem chen_infinite_of_rate_lower_bound
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      c * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 ≤ (chenCount x : ℝ)) :
    chenSet.Infinite := by
  rcases h with ⟨c, hc, hf⟩
  exact chen_infinite_of_count_unbounded
    (Commons.Analysis.Asymptotics.unbounded_of_eventually_ge_mul_div_log_sq (F := chenCount) hc hf)

end Submission

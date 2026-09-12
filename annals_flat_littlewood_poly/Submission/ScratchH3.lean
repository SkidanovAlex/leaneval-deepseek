import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission.Sec3H

/-- auxiliary arithmetic bound for the H approximation -/
lemma H_bound_aux (k : ℕ) (hk : k ≤ 4) :
    (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))))) +
      (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (k - i))))) ≤ 1 / 8 := by
  interval_cases k <;> norm_num [Finset.sum_range_succ]

end Submission.Sec3H

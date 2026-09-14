import ChallengeDeps
import Submission.Vdw.Counting
import Submission.Commons.Analysis.Asymptotics.Ints.pow_two_mul_add_one
import Submission.Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le

open vanDerWaerdenConjecture
open Function Polynomial Filter Asymptotics

set_option autoImplicit false

/-!
# Asymptotic plumbing for `E n H`

Trivial big-O consequences of the counting bounds in `Submission.Vdw.Counting`.
These demonstrate the filter/`IsBigO` idioms used in the main theorem: bounds of
the form "for all large `H`, `f H ≤ C * H ^ k`" translate into big-O statements
for the real-valued functions on `ℕ`.
-/

namespace Submission.Vdw

/-- The total number `(2H+1)^n` of polynomials in the box is `O(H^n)`. -/
theorem boxCard_isBigO (n : ℕ) :
    (fun H : ℕ => (((2 * H + 1 : ℕ) ^ n : ℕ) : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ n : ℝ)) := by
  simpa using (Commons.Analysis.Asymptotics.Ints.pow_two_mul_add_one n)

/-- `E n H` is bounded by the number of polynomials in the box, pointwise. -/
theorem E_le_boxCard (n H : ℕ) : E n H ≤ (2 * H + 1) ^ n :=
  E_le_box_card n H

/-- Trivial bound `E n H = O(H^n)`. -/
theorem E_isBigO_pow (n : ℕ) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ n : ℝ)) := by
  have h1 : (fun H : ℕ => (E n H : ℝ)) =O[atTop]
      (fun H : ℕ => (((2 * H + 1 : ℕ) ^ n : ℕ) : ℝ)) := by
    exact Commons.Analysis.Asymptotics.isBigO_of_eventually_le (fun H => E n H)
      (fun H => (2 * H + 1) ^ n) (Filter.Eventually.of_forall (E_le_boxCard n))
  exact h1.trans (boxCard_isBigO n)

end Submission.Vdw

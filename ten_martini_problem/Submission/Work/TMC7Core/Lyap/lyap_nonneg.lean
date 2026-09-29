import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one

/-!
# Nonnegativity of the Lyapunov exponent

The Lyapunov exponent is defined (AJ (2.2)--(2.5)) as the infimum

`lyap α lam E = ⨅ n, (1/(n+1)) ∫₀¹ log ‖A_{n+1}(x)‖_F dx`

of the averaged logarithms of the Frobenius norms of the transfer iterates.  Every
iterate `A_n(x)` of the transfer cocycle has determinant one (`det_iterC`), so
`‖A_n(x)‖_F ≥ √2 > 1` (`frob_sqrt_two_le_of_det_one`), and every term of the family is
therefore `≥ 0`; being an infimum of nonnegative reals, so is `lyap`.

This is the trivial half of AJ's identity `L(E) = inf_n (1/n) ∫ ln ‖A_n‖`; the content
here is only that all the averaged integrands are nonnegative.
-/

namespace Work.TMC7Core.Lyap

/-- Every averaged log-Frobenius term is nonnegative: the transfer iterates have
determinant one, hence Frobenius norm at least `√2 > 1`. -/
theorem integral_log_frob_iterC_nonneg (α lam : ℝ) (E : ℂ) (n : ℕ) :
    0 ≤ (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1) := by
  apply div_nonneg _ (by positivity)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u _
  apply Real.log_nonneg
  have hle : Real.sqrt 2 ≤ frob (iterC α lam E (n + 1) u) :=
    Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam E (n + 1) u)
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  linarith

theorem lyap_nonneg (α lam : ℝ) (E : ℂ) : 0 ≤ lyap α lam E := by
  unfold lyap
  exact le_ciInf fun n => integral_log_frob_iterC_nonneg α lam E n

end Work.TMC7Core.Lyap

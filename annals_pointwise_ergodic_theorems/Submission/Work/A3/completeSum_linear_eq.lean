import Mathlib
import Submission.Work.A3.Circle

/-!
# The complete sum of a *linear* polynomial

If `g : ℤ[X]` has `natDegree = 1`, then `g(X) = g.coeff 0 + g.coeff 1 * X`, so its complete
exponential sum mod `q` factorises:

`completeSum g a q = e(-2πi a·g.coeff 0 / q) · ∑_{r<q} e(-2πi a·g.coeff 1 · r / q)`.

The second factor is the *geometric* sum, evaluated in `Work.A3.sum_range_exp_neg_int_mul_div`;
this file is the reduction step: it separates the constant term of `g` from the linear one.

The statement holds for `q = 0` as well, where both sides vanish (an empty sum equals `0`, and
the right-hand side is multiplied by the empty sum).
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

/-- A polynomial of `natDegree = 1` is its constant term plus its linear term. -/
lemma eval_eq_coeff_zero_add_coeff_one_mul (g : Polynomial ℤ) (hdeg : g.natDegree = 1)
    (x : ℤ) : g.eval x = g.coeff 0 + g.coeff 1 * x := by
  rw [Polynomial.eval_eq_sum_range, hdeg]
  norm_num [Finset.sum_range_succ]

/-- **The complete sum of a linear polynomial.**  The constant term of `g` factors out of the
complete exponential sum, leaving the geometric sum in `g.coeff 1`. -/
lemma completeSum_linear_eq (g : Polynomial ℤ) {q : ℕ} (hdeg : g.natDegree = 1) (a : ℤ) :
    Work.A3.completeSum g a q
      = Complex.exp (-(2 * Real.pi * Complex.I * (((a * g.coeff 0 : ℤ) : ℝ) / (q : ℝ))))
        * ∑ r ∈ Finset.range q,
            Complex.exp (-(2 * Real.pi * Complex.I *
              (((a * g.coeff 1 : ℤ) : ℝ) * (r : ℝ) / (q : ℝ)))) := by
  rw [completeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Complex.exp_add]
  congr 1
  rw [eval_eq_coeff_zero_add_coeff_one_mul g hdeg]
  push_cast
  ring

end

end Work.A3

import Mathlib
import Submission.Work.C17.p2x_defs

namespace Work.C17

/-- Evaluation of the septic `GAB c d` and of its derivative at `α`.
The product rule plus `ring` normalisation. -/
theorem gab_eval (c d α : ℂ) :
    (Work.C17.GAB c d).eval α
        = (α - 1) * α * (α + 1) * ((α ^ 2 - c * α + 1) * (α ^ 2 - d * α + 1)) ∧
      (Work.C17.GAB c d).derivative.eval α
        = (3 * α ^ 2 - 1) * ((α ^ 2 - c * α + 1) * (α ^ 2 - d * α + 1))
          + (α ^ 3 - α) * ((2 * α - c) * (α ^ 2 - d * α + 1)
              + (α ^ 2 - c * α + 1) * (2 * α - d)) := by
  constructor
  · simp only [GAB_def, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one]
  · simp only [GAB_def, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_add,
      Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.derivative_one, Polynomial.derivative_pow,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_zero]
    ring

end Work.C17

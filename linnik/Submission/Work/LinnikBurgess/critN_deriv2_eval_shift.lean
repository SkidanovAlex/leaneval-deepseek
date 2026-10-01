import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.critN_shifts

/-!
# The second derivative of the Wronskian `critN` at the critical point `y`

Let `A = cubicZ a = ∏_l (X + a_l)` and `B = cubicZ b`, so that
`critN a b = A' B - A B'` is the Wronskian of the two cubics, and let
`sh1, sh2, sh3` be the elementary symmetric functions of `(y + a 0, y + a 1, y + a 2)`
(shifted to the point `y`).

Since `critN' = A'' B - A B''` and `critN'' = A''' B + A'' B' - A' B'' - A B'''`, and since
at the shift `y` one has `A(y) = sh3 y a`, `A'(y) = sh2 y a`, `A''(y) = 2 sh1 y a`,
`A'''(y) = 6` (and the same for `b`), evaluating at `y` gives

`critN''(y) = 2 * ((sh1 y a) (sh2 y b) - (sh2 y a) (sh1 y b) - 3 ((sh3 y a) - (sh3 y b)))`.
-/

namespace Work.LinnikBurgess

open Polynomial

/-- The third derivative of the shifted cubic `cubicIn` is the constant `6`. -/
theorem cubicIn_deriv3 (z s1 s2 s3 : ℤ) :
    derivative (derivative (derivative (cubicIn z s1 s2 s3))) = C 6 := by
  rw [cubicIn_deriv2]
  simp

/-- The third derivative of `cubicZ a` evaluated at the shift `y` equals `6`. -/
theorem cubicZ_deriv3_eval_shift (a : Fin 3 → ℕ) (y : ℕ) :
    (derivative (derivative (derivative (cubicZ a)))).eval (y : ℤ) = 6 := by
  rw [cubicZ_eq_cubicIn a y, cubicIn_deriv3]
  simp

/-- The second derivative of the Wronskian `critN a b`, evaluated at the shift `y`. -/
theorem critN_deriv2_eval_shift (a b : Fin 3 → ℕ) (y : ℕ) :
    (Polynomial.derivative (Polynomial.derivative (critN a b))).eval (y : ℤ)
      = 2 * (((sh1 y a : ℤ) * (sh2 y b : ℤ) - (sh2 y a : ℤ) * (sh1 y b : ℤ))
          - 3 * ((sh3 y a : ℤ) - (sh3 y b : ℤ))) := by
  have h3a := cubicZ_deriv3_eval_shift a y
  have h3b := cubicZ_deriv3_eval_shift b y
  simp only [critN, derivative_sub, derivative_mul, derivative_add, eval_sub, eval_add, eval_mul,
    cubicZ_eval_shift, cubicZ_deriv_eval_shift, cubicZ_deriv2_eval_shift, h3a, h3b]
  ring

end Work.LinnikBurgess

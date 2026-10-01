import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.critN_shifts

namespace Work.LinnikBurgess

open Polynomial

/-- Second derivative of the Wronskian `critN a b` evaluated at the shift `y` (a fresh,
`sorry`-free proof of the statement of the still-`sorry`ed
`Work.LinnikBurgess.critN_deriv2_eval_shift`; it must NOT import that module).

Proof: `critN a b = (cubicZ a)' * cubicZ b - cubicZ a * (cubicZ b)'`, so
`(critN a b)'' = (cubicZ a)''' * cubicZ b + (cubicZ a)'' * (cubicZ b)' - (cubicZ a)' * (cubicZ b)''
- cubicZ a * (cubicZ b)'''`; evaluating at `y` with `cubicZ_eval_shift`, `cubicZ_deriv_eval_shift`,
`cubicZ_deriv2_eval_shift` from `critN_shifts` (`f_a(y) = sh3 y a`, `f_a'(y) = sh2 y a`,
`f_a''(y) = 2 sh1 y a`, `f_a'''(y) = 6`) gives
`2(sh1 y a * sh2 y b - sh2 y a * sh1 y b) + 6(sh3 y b - sh3 y a)`, which is exactly
`2*((sh1 y a * sh2 y b - sh2 y a * sh1 y b) - 3*(sh3 y a - sh3 y b))`.  (Alternatively use
`cubicZ_eq_cubicIn` and `cubicIn_deriv2`.) -/
theorem critN_deriv2_eval_shift_sf (a b : Fin 3 → ℕ) (y : ℕ) :
    (Polynomial.derivative (Polynomial.derivative (critN a b))).eval (y : ℤ)
      = 2 * (((sh1 y a : ℤ) * (sh2 y b : ℤ) - (sh2 y a : ℤ) * (sh1 y b : ℤ))
          - 3 * ((sh3 y a : ℤ) - (sh3 y b : ℤ))) := by
  -- The third derivative of `cubicZ c` is the constant `6`, hence evaluates to `6` at `y`:
  -- expand `cubicZ c` around the shift `y` via `cubicZ_eq_cubicIn`, so that the third
  -- derivative is the third derivative of the explicit cubic `cubicIn`, which is `C 6`.
  have h3 : ∀ c : Fin 3 → ℕ,
      (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative (cubicZ c)))).eval
        (y : ℤ) = 6 := by
    intro c
    have hci : Polynomial.derivative (Polynomial.derivative (Polynomial.derivative
        (cubicIn (y : ℤ) (sh1 y c) (sh2 y c) (sh3 y c)))) = Polynomial.C 6 := by
      rw [cubicIn_deriv2]; simp
    rw [cubicZ_eq_cubicIn c y, hci]
    simp
  -- Expand the two derivatives by the product rule and evaluate at `y`.
  simp only [critN, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    cubicZ_eval_shift, cubicZ_deriv_eval_shift, cubicZ_deriv2_eval_shift, h3 a, h3 b]
  ring

end Work.LinnikBurgess

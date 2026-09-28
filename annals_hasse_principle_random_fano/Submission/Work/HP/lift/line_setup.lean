import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.density_aux

/-!
# Setting up the line restriction of a form (for `Work.HP.lift.hensel_lift`)

Given a coefficient vector `a` (a degree-`d` form in `n+1` variables), a point
`x : Fin (n+1) → ℤ` and a coordinate `i`, the function `u ↦ f_a(x + u·e_i)` is a
univariate polynomial with integer coefficients.  `linePoly d n a x i` is that polynomial,
written directly in the monomial basis.

Its two values used by the multivariate Hensel lifting argument are

* `linePoly … .eval 0 = formEval d n a x`,
* `linePoly … .derivative.eval 0 = pderivEval d n a i x`,

and its general value `linePoly … .eval u = formEval d n a (x + Pi.single i u)`.

The file also records the two Taylor congruences (of order one and two) for an arbitrary
integer polynomial that drive the lifting step.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset Polynomial

namespace Work.HP.lift

/-- The restriction of `f_a` to the affine line `x + u • e_i`, as a polynomial in `u`. -/
def linePoly (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    Polynomial ℤ :=
  ∑ m : Mon d n, Polynomial.C (a m) * (Polynomial.C (x i) + Polynomial.X) ^ (m.1 i : ℕ) *
    ∏ j ∈ Finset.univ.erase i, Polynomial.C (x j) ^ (m.1 j : ℕ)

/-- First-order Taylor congruence: `W'(u+h) ≡ W'(u) mod h`. -/
theorem dvd_eval_derivative_sub (W : Polynomial ℤ) (u h : ℤ) :
    h ∣ Polynomial.eval (u + h) W.derivative - Polynomial.eval u W.derivative := by
  simpa using Polynomial.sub_dvd_eval_sub (u + h) u W.derivative

/-- Second-order Taylor congruence:
`W(u+h) ≡ W(u) + h·W'(u) mod h²`. -/
theorem sq_dvd_eval_sub_eval_sub_mul_derivative (W : Polynomial ℤ) (u h : ℤ) :
    h ^ 2 ∣ Polynomial.eval (u + h) W - Polynomial.eval u W - h * Polynomial.eval u W.derivative := by
  obtain ⟨R, hR⟩ : ∃ R, W - Polynomial.C (Polynomial.eval u W) =
      (Polynomial.X - Polynomial.C u) * R :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot])
  have hW : W = (Polynomial.X - Polynomial.C u) * R + Polynomial.C (Polynomial.eval u W) := by
    rw [sub_eq_iff_eq_add] at hR
    exact hR
  have hder : (Polynomial.X - Polynomial.C u : Polynomial ℤ).derivative = 1 := by
    simp [Polynomial.derivative_sub]
  have hR' : Polynomial.eval u W.derivative = Polynomial.eval u R := by
    have hd : W.derivative = R + (Polynomial.X - Polynomial.C u) * R.derivative := by
      rw [hW, Polynomial.derivative_add, Polynomial.derivative_C, add_zero,
        Polynomial.derivative_mul, hder, one_mul]
    rw [hd, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero]
  have key : h * Polynomial.eval (u + h) R =
      Polynomial.eval (u + h) W - Polynomial.eval u W := by
    have e1 : Polynomial.eval (u + h) (W - Polynomial.C (Polynomial.eval u W)) =
        Polynomial.eval (u + h) W - Polynomial.eval u W := by
      simp [Polynomial.eval_sub]
    rw [← e1, hR, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    ring
  have hdiv : h ∣ Polynomial.eval (u + h) R - Polynomial.eval u R := by
    simpa using Polynomial.sub_dvd_eval_sub (u + h) u R
  obtain ⟨S, hS⟩ := hdiv
  refine ⟨S, ?_⟩
  calc Polynomial.eval (u + h) W - Polynomial.eval u W - h * Polynomial.eval u W.derivative
      = h * Polynomial.eval (u + h) R - h * Polynomial.eval u R := by rw [hR', ← key]
    _ = h * (Polynomial.eval (u + h) R - Polynomial.eval u R) := by ring
    _ = h * (h * S) := by rw [hS]
    _ = h ^ 2 * S := by ring

end Work.HP.lift

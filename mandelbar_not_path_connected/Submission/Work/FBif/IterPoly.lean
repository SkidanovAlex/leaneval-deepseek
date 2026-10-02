/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# The antipolynomials of the iterates of `T_c`

`T_c(z) = z̄² + c` is an *antipolynomial*: every iterate `(T_c)^[n]` is of the form
`z ↦ Q_n(star^[n] z)` where `star^[n]` is the `n`-fold conjugation (`z` for `n` even, `z̄` for
`n` odd) and `Q_n ∈ ℂ[X]` is given by the recursion

`Q_0 = X`,  `Q_{n+1} = (Q_n.map star)² + C c`.

This file provides the polynomials `iterP c n` together with the iterate identity
`(T_c)^[n] z = (iterP c n).eval ((star)^[n] z)`.  It is the polynomial model of the
antiholomorphic iterates on which the local expansion at a parabolic point is computed: for
`n = 5` (odd) it exhibits `(T_c)^[5] z = (iterP c 5).eval (star z)` and for `n = 10` (even)
it exhibits the *holomorphic* `(T_c)^[10] z = (iterP c 10).eval z = (Tsq c)^[5] z`.
-/
import Submission.Work.FBif.Cycle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Polynomial
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

namespace Work.FBif

/-! ## Conjugation and polynomial evaluation -/

/-- Conjugation turns evaluation at the conjugate point into evaluation of the conjugate
polynomial: `star (Q.eval (star z)) = (Q.map star).eval z`. -/
theorem star_eval (Q : ℂ[X]) (z : ℂ) :
    star (Q.eval (star z)) = (Q.map (starRingEnd ℂ)).eval z := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add, Polynomial.map_add]
      rw [star_add, hp, hq]
  | monomial n a =>
      simp only [Polynomial.eval_monomial, Polynomial.map_monomial]
      rw [star_mul, star_pow, star_star, starRingEnd_apply, mul_comm]

/-! ## The polynomials of the iterates -/

/-- The polynomials `iterP c n` of the iterates of `T_c`:
`iterP c 0 = X` and `iterP c (n+1) = (iterP c n).map star ^ 2 + C c`. -/
def iterP (c : ℂ) : ℕ → ℂ[X]
  | 0 => Polynomial.X
  | n + 1 => (iterP c n).map (starRingEnd ℂ) ^ 2 + Polynomial.C c

/-- One step of the iterate: `T_c` applied to `Q.eval y`. -/
theorem Tantibar_eval (c : ℂ) (Q : ℂ[X]) (y : ℂ) :
    Tantibar c (Q.eval y) =
      ((Q.map (starRingEnd ℂ)) ^ 2 + Polynomial.C c).eval (star y) := by
  rw [Tantibar]
  rw [show starRingEnd ℂ (Q.eval y) = (Q.map (starRingEnd ℂ)).eval (star y) by
    simpa using star_eval Q (star y)]
  simp [Polynomial.eval_add, Polynomial.eval_pow]

/-- **The iterate identity.**  `(T_c)^[n] z = (iterP c n).eval ((star)^[n] z)`. -/
theorem iterate_iterP (c : ℂ) (n : ℕ) (z : ℂ) :
    (Tantibar c)^[n] z = (iterP c n).eval ((starRingEnd ℂ : ℂ → ℂ)^[n] z) := by
  induction n with
  | zero => simp [iterP]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Tantibar_eval]
    simp only [iterP]
    congr 1
    exact (Function.iterate_succ_apply' (starRingEnd ℂ : ℂ → ℂ) n z).symm

/-! ## The conjugations as iterates -/

theorem star_iterate_two : (starRingEnd ℂ : ℂ → ℂ)^[2] = id := by
  funext x
  simp [Function.iterate_succ_apply']

theorem star_iterate_four : (starRingEnd ℂ : ℂ → ℂ)^[4] = id := by
  have h := Function.iterate_mul (starRingEnd ℂ : ℂ → ℂ) 2 2
  rw [show (4 : ℕ) = 2 * 2 from rfl, h, star_iterate_two]
  simp

theorem star_iterate_five (z : ℂ) : (starRingEnd ℂ : ℂ → ℂ)^[5] z = star z := by
  rw [show (5 : ℕ) = 1 + 4 from rfl, Function.iterate_add_apply, star_iterate_four]
  simp

theorem star_iterate_ten (z : ℂ) : (starRingEnd ℂ : ℂ → ℂ)^[10] z = z := by
  have h := Function.iterate_mul (starRingEnd ℂ : ℂ → ℂ) 2 5
  rw [show (10 : ℕ) = 2 * 5 from rfl, h, star_iterate_two]
  simp

/-! ## The odd and even iterate identities -/

/-- `(T_c)^[5]` is the *antipolynomial* `(iterP c 5).eval (star ·)`. -/
theorem iterP_five_eval_star (c z : ℂ) :
    (iterP c 5).eval (star z) = (Tantibar c)^[5] z := by
  have h : (Tantibar c)^[5] z = (iterP c 5).eval (star z) := by
    rw [iterate_iterP c 5 z, star_iterate_five]
  exact h.symm

/-- `(T_c)^[10]` is the *holomorphic polynomial* `(iterP c 10).eval (·)`. -/
theorem iterP_ten_eval (c z : ℂ) :
    (iterP c 10).eval z = (Tantibar c)^[10] z := by
  have h : (Tantibar c)^[10] z = (iterP c 10).eval z := by
    rw [iterate_iterP c 10 z, star_iterate_ten]
  exact h.symm

end Work.FBif

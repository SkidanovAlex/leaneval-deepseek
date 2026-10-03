import Mathlib.Algebra.Polynomial.Div

namespace Commons.Analysis.Polynomial

open Finset
open scoped BigOperators

/-- Congruence of an integer polynomial modulo `q` along residue classes: for any
`P : ℤ[X]` and integers `q, p, r` one has `q ∣ P (p q + r) − P r`.  This is the arithmetic
input of the circle method: it makes the phase `n ↦ e(a P(n)/q)` `q`-periodic. -/
theorem dvd_eval_sub_eval_mul (P : Polynomial ℤ) (q p r : ℤ) :
    q ∣ P.eval (p * q + r) - P.eval r := by
  have h : p * q + r - r ∣ P.eval (p * q + r) - P.eval r :=
    _root_.Polynomial.sub_dvd_eval_sub (p * q + r) r P
  rw [add_sub_cancel_right] at h
  exact dvd_trans (dvd_mul_left q p) h

end Commons.Analysis.Polynomial
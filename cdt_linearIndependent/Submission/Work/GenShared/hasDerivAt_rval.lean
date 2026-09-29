import Mathlib
import Submission.Work.GenShared.periods_defs

/-!
# `Rval` is the derivative of a rational function

The shared vocabulary `Rval f z = f.num.eval z / f.denom.eval z` reads off the value of a rational
function `f ∈ ℂ(X)` from its canonical numerator/denominator representative, and `dRat f` is the
formal derivative of `f` (`Submission.CDT.dRat`).  This file proves that at every point `z` at which
`f` is regular (`Rreg f z`, i.e. `f.denom.eval z ≠ 0`) the analytic derivative of the function
`w ↦ Rval f w` is `Rval (dRat f) z`.

Two ingredients:

* `Rval_div`: the evaluation `Rval` is well defined on a quotient of polynomials,
  `Rval (A/B) z = A.eval z / B.eval z` whenever `B.eval z ≠ 0`.  (Well-definedness uses that
  `num` and `denom` are coprime: a point where both vanish is impossible, whence the canonical
  denominator does not vanish either.)
* the quotient rule for polynomial evaluations, combined with the fact that
  `dRat f = dRatF f.num f.denom = (num' * denom - num * denom') / denom²` (`Submission.CDT.dRat_eq_dRatF`).

This is the analytic input needed to differentiate expressions such as `Wev` in the
period-independence argument.
-/

namespace Work.GenShared

open Complex Metric Work.GenShared
open Submission.CDT (dRat)

/-- **`Rval` on a quotient of polynomials.**  If `B.eval z ≠ 0` then the rational function `A / B`
evaluates at `z` to `A.eval z / B.eval z` (independently of the chosen representative). -/
theorem Rval_div (A B : Polynomial ℂ) (z : ℂ) (hB : B.eval z ≠ 0) :
    Rval (algebraMap (Polynomial ℂ) (RatFunc ℂ) A / algebraMap (Polynomial ℂ) (RatFunc ℂ) B) z
      = A.eval z / B.eval z := by
  have hB0 : B ≠ 0 := fun h => hB (by rw [h]; simp)
  set g : RatFunc ℂ :=
    algebraMap (Polynomial ℂ) (RatFunc ℂ) A / algebraMap (Polynomial ℂ) (RatFunc ℂ) B with hg
  -- `g = A / B` in cross-multiplied form
  have hcross : g.num * B = A * g.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff (x := g) (p := A) (q := B) hB0).mpr hg
  have hev : g.num.eval z * B.eval z = A.eval z * g.denom.eval z := by
    have h := congr_arg (Polynomial.eval z) hcross
    simpa only [Polynomial.eval_mul] using h
  -- the canonical denominator stays nonzero: `num` and `denom` are coprime
  have hdne : g.denom.eval z ≠ 0 := by
    have hae := Polynomial.aeval_ne_zero_of_isCoprime (RatFunc.isCoprime_num_denom g) z
    simp only [Polynomial.aeval_def] at hae
    intro hdz
    have hnum0 : g.num.eval z = 0 := by
      have h : g.num.eval z * B.eval z = 0 := by rw [hev, hdz, mul_zero]
      exact (mul_eq_zero.mp h).resolve_right hB
    rcases hae with h | h
    · exact h hnum0
    · exact h hdz
  show g.num.eval z / g.denom.eval z = A.eval z / B.eval z
  rw [div_eq_div_iff hdne hB, hev]

theorem hasDerivAt_rval (f : RatFunc ℂ) (z : ℂ) (hz : Rreg f z) :
    HasDerivAt (fun w => Rval f w) (Rval (dRat f) z) z := by
  have hBD : (f.denom ^ 2).eval z ≠ 0 := by
    rw [Polynomial.eval_pow]; exact pow_ne_zero 2 hz
  -- `dRat f` in quotient form
  have hdrat : dRat f
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (f.num.derivative * f.denom - f.num * f.denom.derivative)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (f.denom ^ 2) := by
    rw [Submission.CDT.dRat_eq_dRatF]
    simp only [Submission.CDT.dRatF, ← map_pow]
  -- the quotient rule expressed on `Rval`
  have hval : Rval (dRat f) z
      = (f.num.derivative.eval z * f.denom.eval z - f.num.eval z * f.denom.derivative.eval z)
        / f.denom.eval z ^ 2 := by
    rw [hdrat]
    rw [Rval_div _ _ z hBD]
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_mul]
  rw [hval]
  exact (f.num.hasDerivAt z).div (f.denom.hasDerivAt z) hz

end Work.GenShared

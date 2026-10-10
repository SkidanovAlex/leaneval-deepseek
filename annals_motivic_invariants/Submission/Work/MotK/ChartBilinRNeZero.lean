import Mathlib
import Submission.Work.MotK.ChartCompAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK

/-- **`kleinTwBilin pRaC (kleinTwR chartC) ≠ 0`.**

This is the scalar `b(p, R(chart))` of the composite `f ∘ χ` of the two chart maps of the
T-twisted link (`Work.MotK.KleinTwLinkComp1`), needed as a nonzero factor of
`PhiCh K a b h (fhatC K a b h 4)` in `Work.MotK.ChartCompC`.

Intended route: evaluate at the origin, `MvPolynomial.eval (fun _ : Fin 3 => (0:K))`.  Then
`chartC K` becomes `(0,0,0,0,1)`, `pRaC` becomes `pointC = (1,0,1,b/(a·h),0)` and
`kleinTwR (chartC K)` becomes `(0,0,0,a^2*b^2,0)`, so the polar form collapses to `a^4*b^2*h ≠ 0`
(the `b/(a·h)` entry needs `field_simp` with `ha`, `hh`).  Concretely: `intro h0`, take
`h1 := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0:K))) h0`, then
`simp only [kleinTwBilin, kleinTwQ, kleinTwP0, kleinTwR, kleinTwR0, kleinTwR1, kleinTwR2,
kleinTwR3, kleinTwR4, chartC, pRaC, pointC, pRaC_apply, pointC_apply_zero, pointC_apply_two,
pointC_apply_three, Fin.isValue, Matrix.cons_val, Pi.add_apply, MvPolynomial.eval_X,
MvPolynomial.eval_C, map_add, map_mul, map_pow, map_neg, map_sub, map_one, map_zero] at h1`,
then `field_simp at h1`, `ring_nf at h1` and finish with the contradiction
`a^4*b^2*h ≠ 0` from `ha, hb, hh` (e.g. `mul_eq_zero.mp` twice, or `pow_ne_zero`). -/
theorem ChartBilinRNeZero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (Work.MotK.pRaC K a b h)
      (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.chartC K)) ≠ 0 := by
  intro h0
  -- Evaluate the alleged vanishing at the origin.
  have h1 := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : K))) h0
  simp only [Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ, Work.MotK.kleinTwP0, Work.MotK.kleinTwR,
    Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2, Work.MotK.kleinTwR3,
    Work.MotK.kleinTwR4, Work.MotK.chartC, Work.MotK.pRaC, Work.MotK.pointC, Fin.isValue,
    Matrix.cons_val, Pi.add_apply, MvPolynomial.eval_X, MvPolynomial.eval_C, map_add, map_mul,
    map_pow, map_neg, map_sub, map_one, map_zero] at h1
  -- Clear the `b / (a * h)` denominator and normalise.
  field_simp at h1
  ring_nf at h1
  exact absurd h1 (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 ha) (pow_ne_zero 2 hb)) hh)

end Work.MotK

import Mathlib
import Submission.Work.MotK.ChartCompAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK

/-- Evaluation of the twisted dual secant quintic at the origin of the chart
`chartC K = (0, X₀, X₁, X₂, 1)`: only the pure `(y 4)^5` term survives, giving `-a^5*b^5*h`. -/
private lemma eval_origin_kleinTwSDualInv (K : Type*) [Field K] (a b h : K) :
    MvPolynomial.eval (fun _ : Fin 3 => (0 : K))
      (Work.MotK.kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.chartC K)) = -(a ^ 5 * b ^ 5 * h) := by
  simp only [Work.MotK.kleinTwSDualInv, Work.MotK.chartC, Fin.isValue, Matrix.cons_val,
    MvPolynomial.eval_X, MvPolynomial.eval_C, map_add, map_mul, map_pow, map_sub,
    map_one, map_zero]
  first | refl_ring1 | ring

/-- **`kleinTwSDualInv (C a) (C b) (C h) (chartC K) ≠ 0`.**

This is the value `s'(chart)` of the (inverse-twisted) dual secant quintic on the affine chart of
the T-twisted link (`Work.MotK.KleinTwLinkComp1`), needed as a nonzero factor of
`PhiCh K a b h (fhatC K a b h 4)` in `Work.MotK.ChartCompC`.

Intended route: evaluate at the origin, `MvPolynomial.eval (fun _ : Fin 3 => (0:K))`.  With
`chartC K = (0, X₀, X₁, X₂, 1)` this kills every term of `kleinTwSDualInv` except the pure
`(y 4)^5` term, so the value is the pure monomial `-a^5*b^5*h ≠ 0`.  Concretely: `intro h0`, take
`h1 := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0:K))) h0`, then
`simp only [kleinTwSDualInv, chartC, Fin.isValue, Matrix.cons_val, MvPolynomial.eval_X,
MvPolynomial.eval_C, map_add, map_mul, map_pow, map_neg, map_sub, map_one, map_zero] at h1`
followed by `norm_num at h1` (which yields `(a = 0 ∨ b = 0) ∨ h = 0`) and `tauto`; if `norm_num`
does not split the product, use `mul_eq_zero`/`pow_eq_zero` explicitly. -/
theorem ChartSdualNeZero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (Work.MotK.chartC K) ≠ 0 := by
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : K))) h0
  rw [eval_origin_kleinTwSDualInv K a b h, map_zero] at h1
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 5 ha) (pow_ne_zero 5 hb)) hh)
    (neg_eq_zero.mp h1)

end Work.MotK

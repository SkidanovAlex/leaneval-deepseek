import Mathlib
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- `reverse P = X ^ P.natDegree * P(1/X)`, i.e. evaluating `P` at the uniformizer
`infU E = 1/x` and clearing the denominator `x ^ P.natDegree` gives the reversed polynomial
evaluated at `x`.  This is the algebraic identity behind "the pole order at infinity of `P(x,y)`
is the degree of the reversed polynomial in `1/x`".

Proof: `reverse P = reflect P.natDegree P` and `reflect` is an involution
(`Polynomial.reflect_reflect`), so the general identity `Polynomial.eval₂_reflect_mul_pow`
(which is `eval₂ i (⅟x) (reflect N f) * x ^ N = eval₂ i x f` for `f.natDegree ≤ N`)
applied to `f = P.reverse` and `N = P.natDegree` is exactly what we need, once we replace
`⅟x` by `x⁻¹` (the `Invertible` instance comes from `genX E ≠ 0`). -/
theorem aeval_infU_mul_pow_eq_aeval_reverse (L : Type*) [Field L] (E : WeierstrassCurve L)
    (P : Polynomial L) :
    Polynomial.aeval (Work.MotC2.infU E) P * (Work.MotC2.genX E) ^ P.natDegree =
      Polynomial.aeval (Work.MotC2.genX E) P.reverse := by
  have hx : genX E ≠ 0 := genX_ne_zero E
  haveI : Invertible (genX E) := invertibleOfNonzero hx
  -- `reflect` is an involution, and `reverse P` is `reflect P.natDegree P` by definition.
  have h1 : Polynomial.reflect P.natDegree P.reverse = P := by
    simp only [Polynomial.reverse]
    exact Polynomial.reflect_reflect
  have key := Polynomial.eval₂_reflect_mul_pow (algebraMap L (Func E)) (genX E) P.natDegree
    P.reverse (Polynomial.reverse_natDegree_le P)
  rw [h1, invOf_eq_inv] at key
  rw [Polynomial.aeval_def]
  exact key

end Work.MotC2

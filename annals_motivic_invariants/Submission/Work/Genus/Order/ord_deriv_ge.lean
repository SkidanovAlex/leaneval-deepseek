import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_div
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.ord_pow
import Submission.Work.Genus.Order.min_ord_le_ord_add
import Submission.Work.Genus.Order.multiplicity_derivative_mul_sub_ge
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

open Polynomial

/-- **The derivative of a rational function as an explicit fraction.**  Writing `p = f.num` and
`q = f.denom` for the reduced numerator and denominator of `f`, the quotient rule gives
`deriv f = (p' * q - p * q') / q ^ 2`.  This is `Work.Genus.deriv` with the numerator and the
denominator assembled inside the image of `F[X]` (`map_sub`, `map_mul`, `map_pow`). -/
theorem deriv_eq_div {F : Type*} [Field F] (f : RatFunc F) :
    deriv f = algebraMap (Polynomial F) (RatFunc F)
        (f.num.derivative * f.denom - f.num * f.denom.derivative)
      / algebraMap (Polynomial F) (RatFunc F) (f.denom ^ 2) := by
  rw [Work.Genus.deriv]
  simp only [map_sub, map_mul, map_pow]

/-- **Derivative bound at a finite place.**  Differentiating can lower the order of vanishing at an
irreducible place by at most one: `ord π (deriv f) ≥ ord π f - 1`.

Route: `deriv f = A / q²` with `A = f.num.derivative * f.denom - f.num * f.denom.derivative`
(so `Work.Genus.ord_div` computes `ord π (deriv f) = multiplicity π A - 2 * multiplicity π q`);
then `multiplicity π A ≥ multiplicity π f.num + multiplicity π f.denom - 1` because
`multiplicity π g.derivative ≥ multiplicity π g - 1` (`π^(j-1) ∣ g.derivative` if `π^j ∣ g`, for
`j = multiplicity π g`), so `multiplicity π (g.derivative * h) ≥ multiplicity π g - 1 +
multiplicity π h` and `multiplicity π (a - b) ≥ min (multiplicity π a) (multiplicity π b)`. -/
theorem ord_deriv_ge {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π) {f : RatFunc F}
    (hf : f ≠ 0) (hf' : Work.Genus.deriv f ≠ 0) :
    Work.Genus.ord π f - 1 ≤ Work.Genus.ord π (Work.Genus.deriv f) := by
  have ha : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hb : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  set P := f.num.derivative * f.denom - f.num * f.denom.derivative with hPdef
  set Q := f.denom ^ 2 with hQdef
  -- `deriv f` as the explicit fraction `P / Q` of polynomials
  have hderiv : Work.Genus.deriv f
      = algebraMap (Polynomial F) (RatFunc F) P / algebraMap (Polynomial F) (RatFunc F) Q := by
    rw [deriv_eq_div, hPdef, hQdef]
  -- `P` does not vanish, since otherwise `deriv f = 0`, contrary to the hypothesis
  have hP : P ≠ 0 := by
    intro h
    exact hf' (by rw [hderiv, h, map_zero, zero_div])
  have hQ : Q ≠ 0 := by rw [hQdef]; exact pow_ne_zero 2 hb
  -- `ord_div` on the explicit fraction, together with `multiplicity π (q ^ 2) = 2 * multiplicity π q`
  have hord : Work.Genus.ord π (Work.Genus.deriv f)
      = (multiplicity π P : ℤ) - 2 * (multiplicity π f.denom : ℤ) := by
    rw [hderiv, ord_div hπ hP hQ, hQdef, multiplicity_pow_of_irreducible hπ hb 2]
    push_cast
    first | refl_ring1 | ring
  -- the polynomial multiplicity bound
  have hmain : (multiplicity π f.num : ℤ) + (multiplicity π f.denom : ℤ) - 1
      ≤ (multiplicity π P : ℤ) := by
    rw [hPdef]
    exact multiplicity_derivative_mul_sub_ge hπ ha hb (by rw [← hPdef]; exact hP)
  rw [hord]
  simp only [Work.Genus.ord]
  linarith

end Work.Genus.Order

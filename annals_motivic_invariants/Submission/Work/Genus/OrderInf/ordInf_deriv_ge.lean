import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.OrderInf.ordInf_div
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.ordInf_polynomial
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

open Polynomial

/-- **The `natDegree` bound behind the derivative bound at infinity.**  For polynomials `p`, `q`
over a field, the numerator `p' * q - p * q'` of the quotient rule has `natDegree` at most
`natDegree p + natDegree q - 1` (truncated subtraction).

Route: `natDegree (p' * q)`, the term of the difference, is bounded by
`natDegree p' + natDegree q ≤ (natDegree p - 1) + natDegree q ≤ natDegree p + natDegree q - 1`
using `Polynomial.natDegree_derivative_le` — the inequality that holds in *every* characteristic,
unlike the equality `natDegree p' = natDegree p - 1` which needs `IsAddTorsionFree` — and likewise
for `p * q'` (note that this needs no case distinction: if `p` is a constant then `p' = 0` and the
bound is immediate); finally `natDegree (a - b) ≤ max (natDegree a) (natDegree b)`. -/
theorem natDegree_deriv_num_le {F : Type*} [Field F] (p q : Polynomial F) :
    (p.derivative * q - p * q.derivative).natDegree ≤ p.natDegree + q.natDegree - 1 := by
  have h1 : (p.derivative * q).natDegree ≤ p.natDegree + q.natDegree - 1 := by
    rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
    · rw [derivative_of_natDegree_zero hn, zero_mul]
      simp
    · have hnd : p.derivative.natDegree ≤ p.natDegree - 1 := natDegree_derivative_le p
      have hmul := natDegree_mul_le (p := p.derivative) (q := q)
      calc (p.derivative * q).natDegree ≤ p.derivative.natDegree + q.natDegree := hmul
        _ ≤ (p.natDegree - 1) + q.natDegree := by omega
        _ ≤ p.natDegree + q.natDegree - 1 := by omega
  have h2 : (p * q.derivative).natDegree ≤ p.natDegree + q.natDegree - 1 := by
    rcases Nat.eq_zero_or_pos q.natDegree with hm | hm
    · rw [derivative_of_natDegree_zero hm, mul_zero]
      simp
    · have hnd : q.derivative.natDegree ≤ q.natDegree - 1 := natDegree_derivative_le q
      have hmul := natDegree_mul_le (p := p) (q := q.derivative)
      calc (p * q.derivative).natDegree ≤ p.natDegree + q.derivative.natDegree := hmul
        _ ≤ p.natDegree + (q.natDegree - 1) := by omega
        _ ≤ p.natDegree + q.natDegree - 1 := by omega
  calc (p.derivative * q - p * q.derivative).natDegree
      ≤ max (p.derivative * q).natDegree (p * q.derivative).natDegree := natDegree_sub_le _ _
    _ ≤ p.natDegree + q.natDegree - 1 := max_le h1 h2

/-- **Derivative bound at infinity.**  `ordInf (deriv f) ≥ ordInf f + 1`: differentiating a
rational function increases its order at infinity by at least one.  Route: with `f = p/q`
(`q = f.denom`) and `A = p.derivative * q - p * q.derivative`, `deriv f = A / q²` and
`ordInf (deriv f) = ordInf A - 2 * ordInf q` (`ordInf_div`, all factors non-zero by `hf`, `hf'`);
now `natDegree A ≤ natDegree p + natDegree q - 1` because `natDegree p.derivative ≤ natDegree p - 1`
and `natDegree q.derivative ≤ natDegree q - 1` hold in every characteristic, hence
`ordInf A ≥ ordInf p + ordInf q + 1`. -/
theorem ordInf_deriv_ge {F : Type*} [Field F] {f : RatFunc F} (hf : f ≠ 0)
    (hf' : Work.Genus.deriv f ≠ 0) :
    Work.Genus.ordInf f + 1 ≤ Work.Genus.ordInf (Work.Genus.deriv f) := by
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  set A : Polynomial F := f.num.derivative * f.denom - f.num * f.denom.derivative with hAdef
  -- `deriv f` as the explicit fraction `A / q ^ 2` of polynomials
  have hderiv : Work.Genus.deriv f
      = algebraMap (Polynomial F) (RatFunc F) A
        / algebraMap (Polynomial F) (RatFunc F) (f.denom ^ 2) := by
    rw [Work.Genus.deriv, hAdef]
    simp only [map_sub, map_mul, map_pow]
  -- `A ≠ 0`, since otherwise `deriv f = 0`, contrary to the hypothesis
  have hA : A ≠ 0 := by
    intro h0
    exact hf' (by rw [hderiv, h0, map_zero, zero_div])
  -- order at infinity of `f`, read off the reduced form `f = p / q`
  have hf_ord : Work.Genus.ordInf f = (f.denom.natDegree : ℤ) - (f.num.natDegree : ℤ) := by
    simp only [Work.Genus.ordInf, RatFunc.intDegree]
    first | refl_ring1 | ring
  -- order at infinity of `deriv f = A / q ^ 2`
  have hdv_ord : Work.Genus.ordInf (Work.Genus.deriv f)
      = -(A.natDegree : ℤ) + 2 * (f.denom.natDegree : ℤ) := by
    rw [hderiv, ordInf_div (RatFunc.algebraMap_ne_zero hA)
      (RatFunc.algebraMap_ne_zero (pow_ne_zero 2 hq))]
    simp only [ordInf_polynomial, Polynomial.natDegree_pow]
    push_cast
    first | refl_ring1 | ring
  -- at least one of `p`, `q` is non-constant: otherwise both are non-zero constants, hence both
  -- derivatives vanish and `A = 0`, contradicting `A ≠ 0`
  have hpos : 0 < f.num.natDegree + f.denom.natDegree := by
    by_contra hle
    have hp0 : f.num.natDegree = 0 := by omega
    have hq0 : f.denom.natDegree = 0 := by omega
    refine hA ?_
    rw [hAdef, derivative_of_natDegree_zero hp0, derivative_of_natDegree_zero hq0]
    first | refl_ring1 | ring
  -- the `natDegree` bound transported to `ℤ` (here `hpos` makes the truncated subtraction exact)
  have hZ : (A.natDegree : ℤ) ≤ (f.num.natDegree : ℤ) + (f.denom.natDegree : ℤ) - 1 := by
    have hnat := natDegree_deriv_num_le (F := F) f.num f.denom
    rw [← hAdef] at hnat
    have hcast : ((f.num.natDegree + f.denom.natDegree - 1 : ℕ) : ℤ)
        = (f.num.natDegree : ℤ) + (f.denom.natDegree : ℤ) - 1 := by
      have h1 : 1 ≤ f.num.natDegree + f.denom.natDegree := hpos
      omega
    rw [← hcast]
    exact_mod_cast hnat
  rw [hf_ord, hdv_ord]
  linarith

end Work.Genus.OrderInf

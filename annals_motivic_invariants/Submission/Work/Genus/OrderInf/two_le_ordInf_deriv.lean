import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.OrderInf.ordInf_div
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.ordInf_polynomial
import Submission.Work.Genus.OrderInf.natDegree_derivA_le_of_lt
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

/-- **Equal-degree case, reduced to the strict case by a shift.**  If `1 ≤ natDegree q` and
`natDegree p = natDegree q`, put `c = leadingCoeff p / leadingCoeff q` and
`p̃ = p - C c * q`.  Then `natDegree p̃ < natDegree q` (the `X^(natDegree q)`-coefficients cancel),
and the quotient-rule numerator is unchanged: `p̃' q - p̃ q' = p' q - p q'`.  Hence the strict case
`natDegree_derivA_le_of_lt` applies. -/
theorem natDegree_derivA_le_of_eq_shift {F : Type*} [Field F] (p q : Polynomial F) (hq : q ≠ 0)
    (hn : 1 ≤ q.natDegree) (heq : p.natDegree = q.natDegree) :
    ((p.derivative * q - p * q.derivative).natDegree : ℤ) ≤ 2 * (q.natDegree : ℤ) - 2 := by
  have hlcq : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  set c : F := p.leadingCoeff / q.leadingCoeff with hc
  -- the shifted polynomial has strictly smaller degree
  have hshift : (p - C c * q).natDegree < q.natDegree := by
    have hle : (p - C c * q).natDegree ≤ q.natDegree - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hleN : q.natDegree ≤ N := by omega
      rw [coeff_sub, coeff_C_mul]
      rcases eq_or_lt_of_le hleN with heqN | hltN
      · have hpN : p.coeff N = p.leadingCoeff := by rw [← heqN, ← heq, coeff_natDegree]
        have hqN : q.coeff N = q.leadingCoeff := by rw [← heqN, coeff_natDegree]
        rw [hpN, hqN, hc, div_mul_cancel₀ _ hlcq, sub_self]
      · rw [coeff_eq_zero_of_natDegree_lt (heq ▸ hltN),
            coeff_eq_zero_of_natDegree_lt hltN, mul_zero, sub_zero]
    omega
  -- the quotient-rule numerator is unchanged by the shift
  have hAeq : (p - C c * q).derivative * q - (p - C c * q) * q.derivative
      = p.derivative * q - p * q.derivative := by
    simp only [derivative_sub, derivative_C_mul]
    first | refl_ring1 | ring
  have := natDegree_derivA_le_of_lt (F := F) (p - C c * q) q hq hshift
  rwa [hAeq] at this

/-- **The `natDegree` bound behind the second-order vanishing at infinity.**  If `q ≠ 0` and
`natDegree p ≤ natDegree q`, and the quotient-rule numerator `A = p' q - p q'` is nonzero, then
`natDegree A ≤ 2 * natDegree q - 2` (in `ℤ`). -/
theorem natDegree_derivA_le {F : Type*} [Field F] (p q : Polynomial F) (hq : q ≠ 0)
    (hdeg : p.natDegree ≤ q.natDegree)
    (hA : p.derivative * q - p * q.derivative ≠ 0) :
    ((p.derivative * q - p * q.derivative).natDegree : ℤ) ≤ 2 * (q.natDegree : ℤ) - 2 := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact natDegree_derivA_le_of_lt p q hq hlt
  · have hn : 1 ≤ q.natDegree := by
      by_contra hc
      have h0 : q.natDegree = 0 := by omega
      have hp0 : p.natDegree = 0 := by omega
      exact hA (by rw [derivative_of_natDegree_zero hp0, derivative_of_natDegree_zero h0]; ring)
    exact natDegree_derivA_le_of_eq_shift p q hq hn heq

/-- **The derivative of a function holomorphic at infinity vanishes there to order at least `2`**
(the `u²` in `d/dt = -u² d/du`, `u = 1/t`).  Route: with `f = p/q` and `deg p ≤ deg q` (from
`0 ≤ ordInf f`), `deriv f = A/q²`, `A = p' q - p q'`, and `natDegree A ≤ 2 * natDegree q - 2`: if
`deg p < deg q` then `natDegree A ≤ natDegree p + natDegree q - 1`; if `deg p = deg q = n` the
`X^(2n-1)`-coefficients of `p' q` and `p q'` are both `n * leadingCoeff p * leadingCoeff q`, so
they cancel (in every characteristic, including where `n = 0`). -/
theorem two_le_ordInf_deriv {F : Type*} [Field F] {f : RatFunc F} (hf : f ≠ 0)
    (hf' : Work.Genus.deriv f ≠ 0) (h : 0 ≤ Work.Genus.ordInf f) :
    2 ≤ Work.Genus.ordInf (Work.Genus.deriv f) := by
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  set A : Polynomial F := f.num.derivative * f.denom - f.num * f.denom.derivative with hAdef
  -- `deriv f` as the explicit fraction `A / q ^ 2` of polynomials
  have hderiv : Work.Genus.deriv f
      = algebraMap (Polynomial F) (RatFunc F) A
        / algebraMap (Polynomial F) (RatFunc F) (f.denom ^ 2) := by
    rw [Work.Genus.deriv, hAdef]
    simp only [map_sub, map_mul, map_pow]
  -- `A ≠ 0`, since otherwise `deriv f = 0`
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
  have hdeg : f.num.natDegree ≤ f.denom.natDegree := by
    have h0 : (0 : ℤ) ≤ (f.denom.natDegree : ℤ) - (f.num.natDegree : ℤ) := by
      rw [← hf_ord]; exact h
    omega
  have hbound := natDegree_derivA_le (F := F) f.num f.denom hq hdeg (hAdef ▸ hA)
  rw [← hAdef] at hbound
  rw [hdv_ord]
  linarith

end Work.Genus.OrderInf

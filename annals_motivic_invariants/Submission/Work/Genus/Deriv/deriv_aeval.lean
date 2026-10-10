import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Deriv.deriv_algebraMap
import Submission.Work.Genus.Deriv.deriv_add
import Submission.Work.Genus.Deriv.deriv_mul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Deriv

open Polynomial

/-! ### Two elementary pieces used below

The Leibniz rule for `Work.Genus.deriv` is the one expensive ingredient of the chain rule: the
monomial step of `Polynomial.induction_on` multiplies by `X`, so one needs
`deriv (f * g) = deriv f * g + f * deriv g`.  We supply a short self-contained proof of it here,
directly from `derivAux` and `RatFunc.num_denom_mul` (this keeps the file independent of the
statement of the sibling lemma `deriv_mul`). -/

/-- The quotient rule is multiplicative in the pair representation: applied to the "product" pair
`(p₁ p₂, q₁ q₂)` — which represents `(p₁/q₁) * (p₂/q₂)` — it equals
`derivAux p₁ q₁ * (p₂/q₂) + (p₁/q₁) * derivAux p₂ q₂`.  A single `field_simp`/`ring` computation
using the product rule for `Polynomial.derivative`. -/
private theorem derivAux_mul {F : Type*} [Field F] (p₁ p₂ q₁ q₂ : Polynomial F)
    (h₁ : q₁ ≠ 0) (h₂ : q₂ ≠ 0) :
    derivAux (p₁ * p₂) (q₁ * q₂)
      = derivAux p₁ q₁
          * (algebraMap (Polynomial F) (RatFunc F) p₂ / algebraMap (Polynomial F) (RatFunc F) q₂)
        + (algebraMap (Polynomial F) (RatFunc F) p₁ / algebraMap (Polynomial F) (RatFunc F) q₁)
          * derivAux p₂ q₂ := by
  have hQ₁ : algebraMap (Polynomial F) (RatFunc F) q₁ ≠ 0 := RatFunc.algebraMap_ne_zero h₁
  have hQ₂ : algebraMap (Polynomial F) (RatFunc F) q₂ ≠ 0 := RatFunc.algebraMap_ne_zero h₂
  simp only [derivAux, derivative_mul]
  simp only [map_add, map_mul]
  field_simp
  first | refl_ring1 | ring

/-- The Leibniz rule for the formal derivative on `F(t)`, proved from `derivAux_mul` and
`RatFunc.num_denom_mul` (the quotient-rule expression is independent of the chosen representation of
the rational function). -/
private theorem deriv_mul' {F : Type*} [Field F] (f g : RatFunc F) :
    Work.Genus.deriv (f * g) = Work.Genus.deriv f * g + f * Work.Genus.deriv g := by
  rw [deriv_eq_derivAux (f * g),
    derivAux_congr (RatFunc.denom_ne_zero (f * g))
      (mul_ne_zero f.denom_ne_zero g.denom_ne_zero) (RatFunc.num_denom_mul f g),
    derivAux_mul f.num g.num f.denom g.denom f.denom_ne_zero g.denom_ne_zero]
  simp only [deriv_eq_derivAux f, deriv_eq_derivAux g, RatFunc.num_div_denom]

/-- The value of `aeval x (derivative (B * X)) * deriv x`, resolved once and for all: it is
`(aeval x (derivative B) * x + aeval x B) * deriv x`.  This is just the product rule for
`Polynomial.derivative` together with `aeval_add`, `aeval_mul`, `aeval_X`. -/
private theorem aeval_deriv_mul_X {F : Type*} [Field F] (x : RatFunc F) (B : Polynomial F) :
    Polynomial.aeval x (Polynomial.derivative (B * Polynomial.X)) * Work.Genus.deriv x
      = (Polynomial.aeval x (Polynomial.derivative B) * x + Polynomial.aeval x B)
          * Work.Genus.deriv x := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, Polynomial.aeval_add,
    Polynomial.aeval_mul, Polynomial.aeval_X]

/-- **The chain rule for the formal derivative on `F(t)`.**  For a polynomial `A` and `x : F(t)`,
`deriv (A(x)) = A'(x) * deriv x`.  Route: induction on `A` (`Polynomial.induction_on`) using
`Polynomial.aeval_add`, `aeval_mul`, `aeval_C`, `aeval_X` together with `Work.Genus.deriv_algebraMap`,
`Work.Genus.deriv_add` and `Work.Genus.deriv_mul`. -/
theorem deriv_aeval {F : Type*} [Field F] {A : Polynomial F} {x : RatFunc F} :
    Work.Genus.deriv (Polynomial.aeval x A)
      = Polynomial.aeval x (Polynomial.derivative A) * Work.Genus.deriv x := by
  induction A using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.aeval_C, Polynomial.derivative_C]
      have hC : algebraMap F (RatFunc F) a
          = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C a) := by
        rw [show (Polynomial.C a : Polynomial F) = algebraMap F (Polynomial F) a from rfl]
        exact (IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F) a).symm
      rw [hC, deriv_algebraMap]
      simp
  | add p q hp hq =>
      rw [Polynomial.aeval_add, Polynomial.derivative_add, Polynomial.aeval_add,
        deriv_add, hp, hq]
      first | refl_ring1 | ring
  | monomial n a ih =>
      have hpow : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial F)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [hpow]
      rw [aeval_deriv_mul_X]
      conv_lhs => rw [Polynomial.aeval_mul, Polynomial.aeval_X]
      rw [deriv_mul', ih]
      first | refl_ring1 | ring

end Work.Genus.Deriv

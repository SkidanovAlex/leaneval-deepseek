/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# Multiplication of the `(P + P'·w)` normal forms

In the function field `L(E) = Func E` of a Weierstrass curve `E` over a field `L`, let
`x = genX E`, `w = infW E = y/x²`.  Every element of the chart-at-infinity coordinate ring is
written in the normal form `Tgen E P Q + Tgen E P' Q' · w`, with `Tgen E P Q = P(x)/Q(x)`.

Multiplication of two such normal forms is closed: the product again has the same shape, with the
numerator/denominator data

* `P₁·P₂·(Q₁'·Q₂'·X⁴) + P₁'·P₂'·cubicPoly E·(Q₁·Q₂)` over `Q₁·Q₂·Q₁'·Q₂'·X⁴` for the `w⁰` part,
* `P₁·P₂'·(Q₂·Q₁'·X²) + P₂·P₁'·(Q₁·Q₂'·X²) - P₁'·P₂'·linPoly E·(Q₁·Q₂)` over
  `Q₁·Q₂·Q₁'·Q₂'·X²` for the `w¹` part.

The only ingredient of the Weierstrass relation that enters is `w²·x⁴ = c(x) - t(x)·w·x²`
(`infW_sq_mul_genX_pow`), used to eliminate `w²`.

## Tags

elliptic curve, function field, chart at infinity
-/

import Mathlib
import Submission.Work.MotC2.PoleTgen
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- A purely ring-theoretic identity: in any field, multiplying two `(p/q + p'/q'·w)` normal forms
and using `w²·x⁴ = c - t·(w·x²)` to eliminate `w²` yields the stated normal form. -/
private lemma Tgen_mul_expansion {F : Type*} [Field F] (p₁ q₁ p₁' q₁' p₂ q₂ p₂' q₂' x w c t : F)
    (hq₁ : q₁ ≠ 0) (hq₁' : q₁' ≠ 0) (hq₂ : q₂ ≠ 0) (hq₂' : q₂' ≠ 0) (hx : x ≠ 0)
    (hw : w ^ 2 * x ^ 4 = c - t * (w * x ^ 2)) :
    (p₁ / q₁ + p₁' / q₁' * w) * (p₂ / q₂ + p₂' / q₂' * w) =
      (p₁ * p₂ * (q₁' * q₂' * x ^ 4) + p₁' * p₂' * c * (q₁ * q₂)) /
        (q₁ * q₂ * (q₁' * q₂' * x ^ 4)) +
      (p₁ * p₂' * (q₂ * q₁' * x ^ 2) + p₂ * p₁' * (q₁ * q₂' * x ^ 2) -
          p₁' * p₂' * t * (q₁ * q₂)) /
        (q₁ * q₂ * (q₁' * q₂' * x ^ 2)) * w := by
  have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 hx
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp
  linear_combination (norm := first | refl_ring1 | ring1) (q₁ * p₁' * q₂ * p₂') * hw

theorem Tgen_mul_witness (L : Type*) [Field L] (E : WeierstrassCurve L)
    (P₁ Q₁ P₁' Q₁' P₂ Q₂ P₂' Q₂' : Polynomial L)
    (h₁ : Q₁ ≠ 0) (h₁' : Q₁' ≠ 0) (h₂ : Q₂ ≠ 0) (h₂' : Q₂' ≠ 0) :
    (Work.MotC2.Tgen E P₁ Q₁ + Work.MotC2.Tgen E P₁' Q₁' * Work.MotC2.infW E) *
        (Work.MotC2.Tgen E P₂ Q₂ + Work.MotC2.Tgen E P₂' Q₂' * Work.MotC2.infW E) =
      Work.MotC2.Tgen E (P₁ * P₂ * (Q₁' * Q₂' * Polynomial.X ^ 4) +
          P₁' * P₂' * Work.MotC2.cubicPoly E * (Q₁ * Q₂)) (Q₁ * Q₂ * (Q₁' * Q₂' * Polynomial.X ^ 4)) +
        Work.MotC2.Tgen E (P₁ * P₂' * (Q₂ * Q₁' * Polynomial.X ^ 2) +
            P₂ * P₁' * (Q₁ * Q₂' * Polynomial.X ^ 2) -
            P₁' * P₂' * Work.MotC2.linPoly E * (Q₁ * Q₂))
          (Q₁ * Q₂ * (Q₁' * Q₂' * Polynomial.X ^ 2)) * Work.MotC2.infW E := by
  have hgen := Tgen_mul_expansion (Polynomial.aeval (Work.MotC2.genX E) P₁)
    (Polynomial.aeval (Work.MotC2.genX E) Q₁) (Polynomial.aeval (Work.MotC2.genX E) P₁')
    (Polynomial.aeval (Work.MotC2.genX E) Q₁') (Polynomial.aeval (Work.MotC2.genX E) P₂)
    (Polynomial.aeval (Work.MotC2.genX E) Q₂) (Polynomial.aeval (Work.MotC2.genX E) P₂')
    (Polynomial.aeval (Work.MotC2.genX E) Q₂') (Work.MotC2.genX E) (Work.MotC2.infW E)
    (Polynomial.aeval (Work.MotC2.genX E) (Work.MotC2.cubicPoly E))
    (Polynomial.aeval (Work.MotC2.genX E) (Work.MotC2.linPoly E))
    (Work.MotC2.aeval_genX_ne_zero E h₁) (Work.MotC2.aeval_genX_ne_zero E h₁')
    (Work.MotC2.aeval_genX_ne_zero E h₂) (Work.MotC2.aeval_genX_ne_zero E h₂')
    (Work.MotC2.genX_ne_zero E) (Work.MotC2.infW_sq_mul_genX_pow E)
  simpa only [Work.MotC2.Tgen_def, div_eq_mul_inv, map_add, map_mul, map_sub, map_pow,
    Polynomial.aeval_X] using hgen

end Work.MotC2

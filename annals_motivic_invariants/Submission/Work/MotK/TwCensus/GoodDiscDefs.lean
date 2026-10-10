/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK.TwCensus
-/
import Mathlib
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Shared definitions for the discriminant non-vanishing lemma

Target: `Work.MotK.TwCensus.GoodDiscNe`.  Everything is built from the explicit certificate for
the "pentagon" degeneracy of the Klein (Pfaffian) quintic `C_{a,b} = V(p₀,…,p₄)`.

Setting `r = b/a`, the discriminant is `Δ = a¹⁰ - 11a⁵b⁵ - b¹⁰ = a¹⁰(1 - 11r⁵ - r¹⁰)`, so
`Δ = 0` is `r¹⁰ + 11r⁵ - 1 = 0`.  In that case the curve degenerates into five lines and the
product of the five hyperplanes is, up to the factor `25`, the form `gdForm25 r` below, which lies
in the ideal `(p₀,…,p₄)` by an explicit twelve-term certificate `gdCertSum`.

All identities here are polynomial identities with integer coefficients, hence hold in every
commutative ring; the fields are only needed to divide by `25` and to cancel `r ≠ 0`.
-/

set_option autoImplicit false

namespace Work.MotK.TwCensus

variable {A : Type*} [Field A]

/-- `α = -(8r² + r⁷)`: the coefficient of `x₀²x₃²x₄` in the degenerate quintic. -/
def gdAlpha (r : A) : A := -(8 * r ^ 2 + r ^ 7)

/-- The twelve coefficients `c₀, …, c₁₁` of the certificate, as polynomials in `r`. -/
def gdC (r : A) : Fin 12 → A :=
  ![-(11 * r ^ 4 + r ^ 9), -(11 * r ^ 3 + r ^ 8), r ^ 2, -r, -r, -(11 * r ^ 2 + r ^ 7),
    r, -r ^ 2, -1, r ^ 4, r ^ 2, -(11 * r ^ 4 + r ^ 9)]

/-- The certificate sum `∑ cᵢ p · monomial` in the normalised Klein coordinates `a = 1`, `b = r`,
so that `p_k = kleinP 1 r x k = -r x_{2k}² + x_{2k+2}x_{2k+3} - r²x_{2k+1}x_{2k+4}`. -/
def gdCertSum (r : A) (x : Fin 5 → A) : A :=
    gdC r 0 * Work.MotK.kleinP 1 r x 0 * x 0 ^ 3
  + gdC r 1 * Work.MotK.kleinP 1 r x 0 * x 0 * x 2 * x 3
  + gdC r 2 * Work.MotK.kleinP 1 r x 0 * x 2 * x 4 ^ 2
  + gdC r 3 * Work.MotK.kleinP 1 r x 0 * x 3 ^ 2 * x 4
  + gdC r 4 * Work.MotK.kleinP 1 r x 1 * x 0 ^ 2 * x 1
  + gdC r 5 * Work.MotK.kleinP 1 r x 1 * x 0 * x 3 ^ 2
  + gdC r 6 * Work.MotK.kleinP 1 r x 1 * x 3 * x 4 ^ 2
  + gdC r 7 * Work.MotK.kleinP 1 r x 2 * x 0 ^ 2 * x 2
  + gdC r 8 * Work.MotK.kleinP 1 r x 2 * x 0 * x 3 * x 4
  + gdC r 9 * Work.MotK.kleinP 1 r x 2 * x 4 ^ 3
  + gdC r 10 * Work.MotK.kleinP 1 r x 3 * x 0 ^ 2 * x 3
  + gdC r 11 * Work.MotK.kleinP 1 r x 4 * x 3 ^ 3

/-- The same certificate sum with general Klein parameters `a`, `b`: the coefficients are
`gdC (b / a)`. -/
def gdCertSumGen (a b : A) (x : Fin 5 → A) : A :=
    gdC (b / a) 0 * Work.MotK.kleinP a b x 0 * x 0 ^ 3
  + gdC (b / a) 1 * Work.MotK.kleinP a b x 0 * x 0 * x 2 * x 3
  + gdC (b / a) 2 * Work.MotK.kleinP a b x 0 * x 2 * x 4 ^ 2
  + gdC (b / a) 3 * Work.MotK.kleinP a b x 0 * x 3 ^ 2 * x 4
  + gdC (b / a) 4 * Work.MotK.kleinP a b x 1 * x 0 ^ 2 * x 1
  + gdC (b / a) 5 * Work.MotK.kleinP a b x 1 * x 0 * x 3 ^ 2
  + gdC (b / a) 6 * Work.MotK.kleinP a b x 1 * x 3 * x 4 ^ 2
  + gdC (b / a) 7 * Work.MotK.kleinP a b x 2 * x 0 ^ 2 * x 2
  + gdC (b / a) 8 * Work.MotK.kleinP a b x 2 * x 0 * x 3 * x 4
  + gdC (b / a) 9 * Work.MotK.kleinP a b x 2 * x 4 ^ 3
  + gdC (b / a) 10 * Work.MotK.kleinP a b x 3 * x 0 ^ 2 * x 3
  + gdC (b / a) 11 * Work.MotK.kleinP a b x 4 * x 3 ^ 3

/-- `25 · F` where `F = x₀⁵ + αx₀²x₃²x₄ - (α³/25)x₀x₃x₄³ + x₃⁵ - r⁵x₄⁵`, written without
division. -/
def gdForm25 (r : A) (x : Fin 5 → A) : A :=
  25 * x 0 ^ 5 + 25 * gdAlpha r * x 0 ^ 2 * x 3 ^ 2 * x 4
    - gdAlpha r ^ 3 * x 0 * x 3 * x 4 ^ 3 + 25 * x 3 ^ 5 + (-25 * r ^ 5) * x 4 ^ 5

/-- `F = x₀⁵ + αx₀²x₃²x₄ - (α³/25)x₀x₃x₄³ + x₃⁵ - r⁵x₄⁵` (the degenerate quintic, which is a
product of five linear forms). -/
def gdForm (r : A) (x : Fin 5 → A) : A :=
  x 0 ^ 5 + gdAlpha r * x 0 ^ 2 * x 3 ^ 2 * x 4 + (-(gdAlpha r) ^ 3 / 25) * x 0 * x 3 * x 4 ^ 3
    + x 3 ^ 5 + (-r ^ 5) * x 4 ^ 5

end Work.MotK.TwCensus

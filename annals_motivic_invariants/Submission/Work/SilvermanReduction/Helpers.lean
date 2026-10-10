/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The chord–tangent identities behind Silverman, *AEC*, VII.2.1

The additivity of the reduction map on points (Silverman VII.2.1) rests on two explicit
identities for the coordinates of a sum of two points of an integral Weierstrass curve; they are
collected here because they are the only non-elementary algebraic input of the proof, and because
in the degenerate cases (`x ≡ u` modulo the maximal ideal, where the slope

  `λ = (y - v)/(x - u)`

is *not* integral) they are what replaces the slope computation.

* `addX_mul_sq` — for `x ≠ u`, the identity
  `(x-u)² · addX x u (slope x u y v) = N(x,y,u,v)`, i.e. the numerator `N` of the
  `x`-coordinate of `(x,y) + (u,v)` cleared of denominators.
* `slope_mul_eq` — the identity `(y-v)(y+v+a₁x+a₃) = (x-u)(x²+xu+u²+a₂(x+u)+a₄-a₁v)`, which
  computes the slope when `x - u` is divisible by the uniformizer.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.SilvermanReduction

noncomputable section

/-- **The chord identity.**  For two points `(x,y)`, `(u,v)` of an integral Weierstrass curve with
`x ≠ u`, twice the `x`-coordinate of their sum, cleared of the denominator `(x-u)²`, is the
polynomial `N`.

This is the identity by which the sum of two points of negative valuation, or of a point of
negative valuation with an integral point, is controlled when the slope is not integral. -/
theorem addX_mul_sq {K : Type*} [Field K] [DecidableEq K] {W : Affine K} {x y u v : K}
    (hx : x ≠ u) (hy : W.Equation x y) (hu : W.Equation u v) :
    (x - u) ^ 2 * W.addX x u (W.slope x u y v)
      = x ^ 2 * u + x * u ^ 2 + 2 * W.a₂ * x * u + W.a₄ * (x + u) + 2 * W.a₆
        - W.a₁ * (x * v + u * y) - W.a₃ * (y + v) - 2 * y * v := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX]
  rw [WeierstrassCurve.Affine.equation_iff] at hy hu
  field_simp
  linear_combination (norm := first | refl_ring1 | ring1) hy + hu

/-- **The slope identity.**  For two points `(x,y)`, `(u,v)` of an integral Weierstrass curve,
`(y-v)·(y+v+a₁x+a₃) = (x-u)·(x²+xu+u²+a₂(x+u)+a₄-a₁v)`; when `x ≡ u` modulo the maximal ideal
this computes the slope as a quotient of two integral quantities whose numerator is a unit of the
residue field (the point being nonsingular). -/
theorem slope_mul_eq {K : Type*} [Field K] {W : Affine K} {x y u v : K}
    (hy : W.Equation x y) (hu : W.Equation u v) :
    (y - v) * (y + v + W.a₁ * x + W.a₃)
      = (x - u) * (x ^ 2 + x * u + u ^ 2 + W.a₂ * (x + u) + W.a₄ - W.a₁ * v) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hy hu
  linear_combination (norm := first | refl_ring1 | ring1) hy - hu

end

end Work.SilvermanReduction

/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Genus
-/
import Mathlib
import ChallengeDeps

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The genus chapter: orders of vanishing and the invariant differential on `ℙ¹`

This is the interface of the area `Submission/Work/Genus`, the **genus / Riemann–Hurwitz chapter**
of the pointless-twist development.  It proves the classical statement that a *constant* elliptic
curve has no non-constant `𝔽(t)`-point, i.e.

  `Work.PointlessTwist.ConstantsOnly 𝔽 E (RatFunc 𝔽)`   (`E(𝔽(t)) = E(𝔽)`),

equivalently: **there is no non-constant morphism `ℙ¹ → E`** (an elliptic curve is not
unirational).  The route is the classical one (see `Submission/Work/PointlessTwist/NOTES.md` §5.1):

* let `ω_E = dx / (2y + a₁x + a₃)` be the invariant differential of `E`; it is regular and nowhere
  vanishing on `E` (`div ω_E = 0`), so its divisor has degree `0`;
* pulling `ω_E` back along a morphism `φ : ℙ¹ → E` (i.e. along the inclusion
  `𝔽(E) ↪ 𝔽(t)`) gives the rational differential `ω = (x'/w) dt` on `ℙ¹` — the *pullback of a
  regular differential is regular*, which is the local analysis formalised here;
* on `ℙ¹` every non-zero rational differential has divisor of degree `2g(ℙ¹) - 2 = -2`; but a
  divisor with all coefficients `≥ 0` has degree `≥ 0`.  Contradiction.

The formalisation is *concrete*: `ℙ¹` is the field `RatFunc 𝔽 = 𝔽(t)` of rational functions, the
places are the irreducible polynomials `π ∈ 𝔽[X]` together with the place at infinity, the order of
vanishing at a place is defined through `Polynomial.multiplicity` of the numerator and denominator
of a rational function (Mathlib's `RatFunc.num`/`RatFunc.denom`), and the differentials on `ℙ¹` are
simply *functions*: the form `f dt` is represented by `f`.

## The definitions

* `ord π f` — the order of vanishing of `f : 𝔽(t)` at the place of the irreducible `π`,
  `= multiplicity π (num f) - multiplicity π (denom f)`, in `ℤ`.
* `ordInf f` — the order of vanishing of `f` at the place at infinity, `= -f.intDegree`; positive
  means a pole at infinity.
* `deriv f` — the formal derivative `d f/dt`, extended from `𝔽[X]` to `𝔽(t)` by the quotient rule.
* `curveCubic E` — the cubic `4X³ + b₂X² + 2b₄X + b₆` whose square root is `2y + a₁x + a₃` on `E`.
-/

set_option autoImplicit false

open Polynomial

namespace Work.Genus

noncomputable section

variable {F : Type*} [Field F]

/-- **The order of vanishing of a rational function at the place of an irreducible polynomial.**
For `f : 𝔽(t)` with numerator `f.num` and denominator `f.denom` (Mathlib's reduced form, `denom`
monic), the order is the multiplicity of `π` in the numerator minus its multiplicity in the
denominator.  Positive means a zero, negative means a pole.  For `f = 0` the value is `0` (the
convention of `Polynomial.multiplicity`); all uses below assume `f ≠ 0`. -/
def ord (π : F[X]) (f : RatFunc F) : ℤ :=
  (multiplicity π f.num : ℤ) - (multiplicity π f.denom : ℤ)

/-- **The order of vanishing of a rational function at the place at infinity.**  It is
`- f.intDegree = deg (f.denom) - deg (f.num)`; positive means a zero and negative a pole, so that
`t` itself has order `-1` there (a pole of order one), exactly as at a finite place. -/
def ordInf (f : RatFunc F) : ℤ := -f.intDegree

/-- **The formal derivative `d/dt` on `𝔽(t)`**, defined by the quotient rule on the reduced
(numerator, denominator) form.  It kills the constants `𝔽` and sends `t` to `1`. -/
def deriv (f : RatFunc F) : RatFunc F :=
  (algebraMap F[X] (RatFunc F) f.num.derivative * algebraMap F[X] (RatFunc F) f.denom
    - algebraMap F[X] (RatFunc F) f.num * algebraMap F[X] (RatFunc F) f.denom.derivative)
    / (algebraMap F[X] (RatFunc F) f.denom) ^ 2

/-- The cubic `4X³ + b₂X² + 2b₄X + b₆` of a Weierstrass curve: the square of the "completed" ordinate
`2y + a₁x + a₃` is its value on the `x`-coordinate.  Its discriminant is `4Δ`, so it is squarefree
exactly when `W` is non-singular (in characteristic `≠ 2`). -/
def curveCubic {R : Type*} [CommRing R] (W : WeierstrassCurve R) : R[X] :=
  4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

@[simp]
theorem curveCubic_eval {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x : R) :
    (curveCubic W).eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [curveCubic]

end

end Work.Genus

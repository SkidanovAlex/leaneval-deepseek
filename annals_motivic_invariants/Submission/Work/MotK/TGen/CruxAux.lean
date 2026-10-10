import Mathlib
import Submission.Work.MotK.TGen.SdG5hDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.CruxAux` — the setup for the crux `sdG5h`

`sdG5h a b h = γ₁x₀⁵ + γ₂x₁⁵ + γ₃x₂⁵ + γ₄x₀²x₁x₂² + γ₅x₀x₁³x₂` with

* `γ₁ = -a⁵b⁵h⁴`, `γ₂ = -a⁵b⁵h³`, `γ₃ = -a⁵b⁵h²`, `γ₄ = h³(3a⁴b⁶-a⁹b)`, `γ₅ = h³(2a⁷b³-a²b⁸)`.

The whole proof goes through the *general* five-coefficient family

`Gg g₁ g₂ g₃ g₄ g₅ = g₁x₀⁵ + g₂x₁⁵ + g₃x₂⁵ + g₄x₀²x₁x₂² + g₅x₀x₁³x₂`:

the target is `Irreducible (Gg γ₁ γ₂ γ₃ γ₄ γ₅)`, and the hypothesis on the discriminant is
exactly the non-vanishing of `γ₅² - 5γ₂γ₄` (the `disc_identity` below).

A homogeneous factor of `Gg` of degree `1` or `2` forces `γ₅² = 5γ₂γ₄`:

* degree 1 (`SdG5hLinearCase`): the substitution killing the linear form and the coefficients of
  `x₁⁵, x₂⁵, x₁⁴x₂, x₁x₂⁴` give `g₁β⁵ = g₂`, `g₁γ⁵ = g₃`, `g₅β = -5g₁β⁴γ`, `g₄γ² = 5g₁βγ⁴`,
  hence `g₅² = 25g₁²β⁶γ² = 5g₂g₄`;
* degree 2 (`SdG5hQuadEquations`, `SdG5hQuadAlg`): writing the factor as
  `x₀² + (px₁+qx₂)x₀ + (rx₁²+sx₁x₂+tx₂²)`, the synthetic division
  `Gg - (R₁x₀+R₀) = (x₀²+Bx₀+C)·Q` (with `R₁`, `R₀` as below) gives a *degree-in-x₀* argument
  `R₁ = R₀ = 0`, and the coefficients of `R₁`, `R₀` give the six equations solved in
  `SdG5hQuadAlg`.

Once a factorization `Gg = F·H` with both factors non-units is given, the top-degree parts give a
factorization by *homogeneous* polynomials (`SdG5hHomogReduce`), one of which has degree `1` or `2`.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The general five-coefficient quintic `g₁x₀⁵+g₂x₁⁵+g₃x₂⁵+g₄x₀²x₁x₂²+g₅x₀x₁³x₂`. -/
noncomputable def Gg (g1 g2 g3 g4 g5 : K) : MvPolynomial (Fin 3) K :=
  C g1 * (X 0) ^ 5 + C g2 * (X 1) ^ 5 + C g3 * (X 2) ^ 5
    + C g4 * ((X 0) ^ 2 * X 1 * (X 2) ^ 2) + C g5 * (X 0 * (X 1) ^ 3 * X 2)

/-- `B = p x₁ + q x₂`, the `x₀`-coefficient of a monic quadratic factor. -/
noncomputable def BB (p q : K) : MvPolynomial (Fin 3) K := C p * X 1 + C q * X 2

/-- `C = r x₁² + s x₁x₂ + t x₂²`, the constant term of a monic quadratic factor. -/
noncomputable def CC (r s t : K) : MvPolynomial (Fin 3) K :=
  C r * (X 1) ^ 2 + C s * X 1 * X 2 + C t * (X 2) ^ 2

/-- The monic homogeneous quadratic `x₀² + Bx₀ + C`. -/
noncomputable def quadF (p q r s t : K) : MvPolynomial (Fin 3) K :=
  (X 0) ^ 2 + BB p q * X 0 + CC r s t

/-- The `x₀`-coefficient of the remainder of `Gg` divided by `quadF` (synthetic division). -/
noncomputable def RR1 (g1 g4 g5 p q r s t : K) : MvPolynomial (Fin 3) K :=
  C g1 * ((BB p q) ^ 4 - 3 * (BB p q) ^ 2 * CC r s t + (CC r s t) ^ 2)
    - C g4 * BB p q * (X 1 * (X 2) ^ 2) + C g5 * ((X 1) ^ 3 * X 2)

/-- The constant term of the remainder of `Gg` divided by `quadF` (synthetic division). -/
noncomputable def RR0 (g1 g2 g3 g4 p q r s t : K) : MvPolynomial (Fin 3) K :=
  C g1 * ((BB p q) ^ 3 * CC r s t - 2 * BB p q * (CC r s t) ^ 2)
    - C g4 * CC r s t * (X 1 * (X 2) ^ 2) + C g2 * (X 1) ^ 5 + C g3 * (X 2) ^ 5

/-- The cubic quotient `Q` of the synthetic division of `Gg` by `quadF`. -/
noncomputable def QQ (g1 g4 p q r s t : K) : MvPolynomial (Fin 3) K :=
  C g1 * (X 0) ^ 3 - C g1 * BB p q * (X 0) ^ 2 + C g1 * ((BB p q) ^ 2 - CC r s t) * X 0
    + (C g4 * (X 1 * (X 2) ^ 2) - C g1 * (BB p q) ^ 3 + 2 * C g1 * BB p q * CC r s t)

/-- **The synthetic division.**  `Gg - (R₁ x₀ + R₀) = quadF · Q`. -/
theorem division_identity (g1 g2 g3 g4 g5 p q r s t : K) :
    Gg g1 g2 g3 g4 g5 - (RR1 g1 g4 g5 p q r s t * X 0 + RR0 g1 g2 g3 g4 p q r s t)
      = quadF p q r s t * QQ g1 g4 p q r s t := by
  rw [Gg, RR1, RR0, quadF, QQ, BB, CC]
  first | refl_ring1 | ring

/-- `sdG5h` is the general quintic at the five specific coefficients. -/
theorem sdG5h_eq_Gg (a b h : K) :
    sdG5h a b h
      = Gg (-(a ^ 5 * b ^ 5 * h ^ 4)) (-(a ^ 5 * b ^ 5 * h ^ 3)) (-(a ^ 5 * b ^ 5 * h ^ 2))
          (h ^ 3 * (3 * a ^ 4 * b ^ 6 - a ^ 9 * b)) (h ^ 3 * (2 * a ^ 7 * b ^ 3 - a ^ 2 * b ^ 8)) := by
  rw [sdG5h, Gg]

/-- The discriminant of the five coefficients is `γ₅² - 5γ₂γ₄ = -h⁶a⁴b⁶·(a¹⁰-11a⁵b⁵-b¹⁰)`. -/
theorem disc_identity (a b h : K) :
    (h ^ 3 * (2 * a ^ 7 * b ^ 3 - a ^ 2 * b ^ 8)) ^ 2
        - 5 * (-(a ^ 5 * b ^ 5 * h ^ 3)) * (h ^ 3 * (3 * a ^ 4 * b ^ 6 - a ^ 9 * b))
      = -(h ^ 6 * a ^ 4 * b ^ 6) * (a ^ 10 - 11 * a ^ 5 * b ^ 5 - b ^ 10) := by
  first | refl_ring1 | ring

end Work.MotK.TGen

/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.CubTRedDefs
import Submission.Work.MotK.TGen.BwVec4Prime

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.CubTPara` — the parametrisation of the cubic surface `cubTRed = 0`

The cubic `cubTRed a b h` (see `Submission/Work/MotK/TGen/CubTRedDefs.lean`) defines the "cone"
divisor of the target side of the `T`-twisted Crauder–Katz link.  Geometrically its zero locus
`D = {cubTRed = 0} ⊂ 𝔸³` is the image of the plane under the inverse link map `P`, and it is
birational to the quadric cone `S' = Q̃ ∩ {b(p,·) = 0} ⊂ ℙ⁴`, which is rational.

This file records the explicit parametrisation.  In the chart `{y₄ = 1}` of the source `ℙ⁴`, the
cone `S'` has coordinates `(y₀,y₃) = (u,v)` and

  `y = (u, -(a·b·u - a²h·v)²/(a·b³·h), 2u - (a·h/b)·v, v, 1)`,

i.e. `Λ(y) = -2ab·y₀ + a²h·y₃ + ab·y₂ = 0` and `kleinTwQ y = 0`.  Applying the link map `P` and
passing to the target chart `{x₀ = 0, x₄ = 1}` gives the parametrisation

  `θ(x_i) = P_{i+1}(y) / P_4(y)`,   `P = kleinTwP`,

which is birational onto `D` with inverse `X ↦ (R_0(X)/R_4(X), R_3(X)/R_4(X))`, `R = kleinTwR`.

## Main definitions

* `paraPt a b h : Fin 5 → K[u,v]` — the point `y` of the cone `S'` above;
* `paraCoord a b h i = P_i(y) : K[u,v]` — the homogeneous coordinates of the parametrised point;
* `thetaMap a b h : K[x₀,x₁,x₂] →ₐ[K] K(u,v)` — the pullback `x_i ↦ paraCoord (i+1) / paraCoord 4`;
* `rvec a b h : Fin 5 → K[x₀,x₁,x₂]` — the components of `R` on the target chart
  `(0, x₀, x₁, x₂, 1)`; `rvec a b h 4 = bwVec a b h 4`;
* `psiMap a b h : K[u,v] →ₐ[K] (K[x₀,x₁,x₂]/(cubTRed))[1/ā]`, `u ↦ rvec 0 / rvec 4`,
  `v ↦ rvec 3 / rvec 4`, where `ā` is the image of `rvec 4`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

noncomputable section

/-- The point of the quadric cone `S'` parametrised by `(u,v) = (y₀,y₃)`, in the source chart
`{y₄ = 1}`, with `y₁ = -(a·b·u - a²h·v)²/(a·b³·h)` and `y₂ = 2u - (a·h/b)·v`. -/
def paraPt (a b h : K) : Fin 5 → MvPolynomial (Fin 2) K :=
  ![X 0,
    C (-(1 / (a * b ^ 3 * h))) * (C (a * b) * X 0 - C (a ^ 2 * h) * X 1) ^ 2,
    C 2 * X 0 - C (a * h / b) * X 1,
    X 1,
    C 1]

/-- The homogeneous coordinates `P_i(y)` of the parametrised point, `P = kleinTwP`. -/
def paraCoord (a b h : K) (i : Fin 5) : MvPolynomial (Fin 2) K :=
  aeval (paraPt a b h) (kleinTwP (C a) (C b) (C h) (fun t => X t) i)

/-- **The parametrisation** `θ : K[x₀,x₁,x₂] →ₐ[K] K(u,v)`, `x_i ↦ P_{i+1}(y)/P₄(y)`. -/
def thetaMap (a b h : K) : MvPolynomial (Fin 3) K →ₐ[K]
    FractionRing (MvPolynomial (Fin 2) K) :=
  aeval ![algebraMap _ _ (paraCoord a b h 1) / algebraMap _ _ (paraCoord a b h 4),
          algebraMap _ _ (paraCoord a b h 2) / algebraMap _ _ (paraCoord a b h 4),
          algebraMap _ _ (paraCoord a b h 3) / algebraMap _ _ (paraCoord a b h 4)]

/-- The components of the inverse link map `R = kleinTwR` on the target chart
`(0, x₀, x₁, x₂, 1)`; `rvec a b h 4 = bwVec a b h 4`. -/
def rvec (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  kleinTwR (C a) (C b) (C h) (chart3 K)

theorem rvec_four (a b h : K) : rvec a b h 4 = bwVec a b h 4 := by
  simp [rvec, bwVec, Work.MotK.kleinTwPi, Work.MotK.pRa_apply, Work.MotK.kleinPointT]

/-- The ideal of the cubic surface. -/
def cubTIdeal (a b h : K) : Ideal (MvPolynomial (Fin 3) K) := Ideal.span {cubTRed a b h}

/-- **The inverse parametrisation** `ψ : K[u,v] →ₐ[K] (K[x]/(cubTRed))[1/ā]`,
`u ↦ R_0/R_4`, `v ↦ R_3/R_4`, where `ā` is the image of `R_4`. -/
def psiMap (a b h : K) :
    MvPolynomial (Fin 2) K →ₐ[K]
      Localization.Away (Ideal.Quotient.mk (cubTIdeal a b h) (rvec a b h 4)) :=
  MvPolynomial.aeval ![
    IsLocalization.mk'
      (Localization.Away (Ideal.Quotient.mk (cubTIdeal a b h) (rvec a b h 4)))
      (Ideal.Quotient.mk (cubTIdeal a b h) (rvec a b h 0))
      ⟨Ideal.Quotient.mk (cubTIdeal a b h) (rvec a b h 4),
        (Submonoid.mem_powers_iff _ _).mpr ⟨1, pow_one _⟩⟩,
    IsLocalization.mk'
      (Localization.Away (Ideal.Quotient.mk (cubTIdeal a b h) (rvec a b h 4)))
      (Ideal.Quotient.mk (cubTIdeal a b h) (rvec a b h 3))
      ⟨Ideal.Quotient.mk (cubTIdeal a b h) (rvec a b h 4),
        (Submonoid.mem_powers_iff _ _).mpr ⟨1, pow_one _⟩⟩]

end

end Work.MotK.TGen

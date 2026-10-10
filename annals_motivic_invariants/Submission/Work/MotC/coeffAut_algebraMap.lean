import Mathlib
import Submission.Work.MotC.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coefficient action on the constants of the twisted function field (`MotC`)

`Work.MotC.coeffAut D` is the action of the Galois generator `σ = D.sigma` on the coefficients of
the function field `L(E)` of the base-changed elliptic curve `E_L = E ⊗_𝕜 L`, where `L/𝕜` is the
cyclic quintic extension of the quintic-twist datum `D`.

The content of this file is the refinement of the defining property of `coeffAut` (that it is an
`𝕜`-algebra automorphism) to its actual effect on the constants: on the subfield `L = D.ext.L` of
`L(E)` it is the Galois automorphism `σ` itself,

  `coeffAut D l = σ l   for l ∈ L`.

This is the first half of the paper's Kummer-type description of the twisted-translation
automorphism `twistAut D τ_P = (σ on coefficients) ∘ τ_P^*`: the automorphism `α = twistAut D τ_P`
restricts to `σ` on the constants `L`, exactly as used in the descent of the quintic twist.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- The coefficient action on the coordinate ring `L[E]` of the base-changed curve sends the
image of a coefficient `l ∈ L` to the image of `σ l`: on the subalgebra `L ⊆ L[E]` it *is* the
Galois automorphism `σ`.

This refines `Work.MotC.coeffCoordEquiv_algebraMap` (which covers the constants `𝕜 ⊆ L`) to all of
`L`; it is the coordinate-ring form of `coeffAut_algebraMap`.  The proof is the description
`algebraMap L L[E] = AdjoinRoot.of _ ∘ C` of the `L`-algebra structure on the coordinate ring
(`AdjoinRoot.algebraMap_eq'`), together with the description `coeffCoordEquiv_of` of
`coeffCoordEquiv` on polynomial representatives. -/
lemma coeffCoordEquiv_algebraMap_L (D : Work.TorsorExistence.QuinticTwist 𝕜) (l : D.ext.L) :
    coeffCoordEquiv D
        (algebraMap D.ext.L (WeierstrassCurve.Affine.CoordinateRing (baseCurve D)) l) =
      algebraMap D.ext.L (WeierstrassCurve.Affine.CoordinateRing (baseCurve D)) (D.sigma l) := by
  have h1 : ∀ m : D.ext.L,
      (algebraMap D.ext.L (WeierstrassCurve.Affine.CoordinateRing (baseCurve D))) m =
        AdjoinRoot.of (WeierstrassCurve.Affine.polynomial (baseCurve D)) (Polynomial.C m) := by
    intro m
    rw [AdjoinRoot.algebraMap_eq' D.ext.L, Polynomial.algebraMap_eq]
    rfl
  rw [h1 l, h1 (D.sigma l), coeffCoordEquiv_of, Polynomial.map_C]
  rfl

theorem coeffAut_algebraMap {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (l : D.ext.L) :
    Work.MotC.coeffAut D
        (algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) l) =
      algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D))
        (D.sigma l) := by
  -- move the constant from `L` to the coordinate ring `L[E]`, then to `L(E)`
  rw [IsScalarTower.algebraMap_apply D.ext.L
    (WeierstrassCurve.Affine.CoordinateRing (Work.MotC.baseCurve D))
    (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) l]
  -- `coeffAut` is the fraction-field extension of `coeffCoordEquiv`
  simp only [Work.MotC.coeffAut, AlgEquiv.ofRingEquiv_apply]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, coeffCoordEquiv_algebraMap_L,
    ← IsScalarTower.algebraMap_apply D.ext.L
      (WeierstrassCurve.Affine.CoordinateRing (Work.MotC.baseCurve D))
      (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) (D.sigma l)]

end

end Work.MotC

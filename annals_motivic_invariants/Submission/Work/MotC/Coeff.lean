import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- The base-changed curve `E_L = E ⊗_𝕜 L`. -/
noncomputable abbrev baseCurve (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    WeierstrassCurve D.ext.L :=
  D.E.baseChange D.ext.L

/-- The Weierstrass polynomial of `E_L` is fixed by the coefficient action of `σ`: the curve is
defined over `𝕜`. -/
theorem map_polynomial_sigma (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    (WeierstrassCurve.Affine.polynomial (baseCurve D)).map
        (↑(Polynomial.mapAlgEquiv D.sigma).toRingEquiv : D.ext.L[X] →+* D.ext.L[X]) =
      WeierstrassCurve.Affine.polynomial (baseCurve D) := by
  simp only [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  simp

/-- **The coefficient (Galois) action on the coordinate ring.**  The ring automorphism of `L[E]`
which applies `σ` to the `L`-coefficients and fixes the classes of `X` and `Y`. -/
noncomputable def coeffCoordEquiv (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    WeierstrassCurve.Affine.CoordinateRing (baseCurve D) ≃+*
      WeierstrassCurve.Affine.CoordinateRing (baseCurve D) :=
  AdjoinRoot.mapRingEquiv (Polynomial.mapAlgEquiv D.sigma).toRingEquiv
    (WeierstrassCurve.Affine.polynomial (baseCurve D))
    (WeierstrassCurve.Affine.polynomial (baseCurve D))
    (by rw [map_polynomial_sigma D])

/-- The coefficient action on the coordinate ring is given by `p ↦ p.map σ`. -/
theorem coeffCoordEquiv_of (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (r : D.ext.L[X]) :
    coeffCoordEquiv D (AdjoinRoot.of _ r) = AdjoinRoot.of _ (r.map D.sigma.toRingHom) := by
  simp [coeffCoordEquiv, Polynomial.mapAlgEquiv]

/-- The coefficient action fixes the constants. -/
theorem coeffCoordEquiv_algebraMap (D : Work.TorsorExistence.QuinticTwist 𝕜) (c : 𝕜) :
    coeffCoordEquiv D
        (algebraMap 𝕜 (WeierstrassCurve.Affine.CoordinateRing (baseCurve D)) c) =
      algebraMap 𝕜 (WeierstrassCurve.Affine.CoordinateRing (baseCurve D)) c := by
  have h1 : (algebraMap 𝕜 (WeierstrassCurve.Affine.CoordinateRing (baseCurve D))) c =
      AdjoinRoot.of (WeierstrassCurve.Affine.polynomial (baseCurve D))
        (Polynomial.C (algebraMap 𝕜 D.ext.L c)) := by
    rw [IsScalarTower.algebraMap_apply 𝕜 D.ext.L
      (WeierstrassCurve.Affine.CoordinateRing (baseCurve D)) c]
    rfl
  rw [h1, coeffCoordEquiv_of, Polynomial.map_C]
  congr 2
  exact D.sigma.commutes c

/-- **The Galois action on the function field `L(E)`**, i.e. `σ` on the coefficients of `L(E)`.

This is the first half of the twisted-translation automorphism of the auditor's node C1: the second
half is the pullback `τ_P^*` of the translation by the marked point `P`, the translation
automorphism of an elliptic function field (chapter `MotC2`). -/
noncomputable def coeffAut (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[𝕜]
      WeierstrassCurve.Affine.FunctionField (baseCurve D) :=
  AlgEquiv.ofRingEquiv
    (f := IsFractionRing.ringEquivOfRingEquiv (coeffCoordEquiv D)) (by
      intro c
      rw [show algebraMap 𝕜 (WeierstrassCurve.Affine.FunctionField (baseCurve D)) c =
          algebraMap (WeierstrassCurve.Affine.CoordinateRing (baseCurve D))
            (WeierstrassCurve.Affine.FunctionField (baseCurve D))
            (algebraMap 𝕜 (WeierstrassCurve.Affine.CoordinateRing (baseCurve D)) c) from
        (IsScalarTower.algebraMap_apply 𝕜 _ _ c).symm]
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, coeffCoordEquiv_algebraMap])

end

end Work.MotC

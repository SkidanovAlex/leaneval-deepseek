import Mathlib
import Submission.Work.MotC2.InfPlace
import Submission.Work.MotC2.Classification

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- The instance searches triggered by the local ring at infinity (an `IsDiscreteValuationRing`
-- presented as a `Subalgebra` of a function field) are slow but terminate; the default
-- `synthInstance.maxHeartbeats` is not enough for them.
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Polynomial

namespace Work.MotK

/-- An element of the function field `L(E)` of a Weierstrass curve which is algebraic over `L` is
already a constant: `L` is (relatively) algebraically closed in `L(E)` — for **every** Weierstrass
curve, singular or not, in any characteristic. Route (all inputs available in the workspace):
`z` algebraic over `L` ⟹ `z` integral over `L` (`IsAlgebraic.isIntegral`) ⟹ integral over the place
`S = Work.MotC2.infPlace E` (`IsIntegral.tower_top`, `L ≤ S ≤ L(E)`) ⟹ `z ∈ S`
(`Work.MotC2.mem_of_isIntegral` for the rational place `S`, whose `IsRatPlace` structure is
assembled from `Work.MotC2.InfPlaceCore.instIsDiscreteValuationRing`, `...residue_field`,
`...frac_field` — no ellipticity needed). Then reduce the minimal polynomial `Q := minpoly L z`
modulo the maximal ideal of `S`: since the residue field is `L` (the map
`c ↦ mk (algebraMap L S c)` is bijective), the residue `z̄` is some `c : L` with `Q c = 0`; as `Q`
is irreducible this forces `Q = X - C c`, whence `z = algebraMap L _ c`. -/
theorem algebraic_mem_base {L : Type} [Field L] (E : WeierstrassCurve L)
    {z : WeierstrassCurve.Affine.FunctionField E} (hz : IsAlgebraic L z) :
    ∃ c : L, z = algebraMap L (WeierstrassCurve.Affine.FunctionField E) c := by
  -- The local ring at infinity, a discrete valuation ring with residue field `L` and fraction
  -- field `L(E)` — `InfPlaceCore` proves all three without any hypothesis on `E`.
  let S : Subalgebra L (WeierstrassCurve.Affine.FunctionField E) := Work.MotC2.infPlace E
  have hS : Work.MotC2.IsRatPlace E S :=
    ⟨⟨Work.MotC2.InfPlaceCore.instIsDiscreteValuationRing E,
      Work.MotC2.InfPlaceCore.residue_field E⟩,
     Work.MotC2.InfPlaceCore.frac_field E⟩
  -- Step 1: `z` is integral over `L`, hence over `S` (tower), hence lies in `S` (a DVR is
  -- integrally closed in its fraction field).
  have hzS : z ∈ S := Work.MotC2.mem_of_isIntegral hS (IsIntegral.tower_top hz.isIntegral)
  -- Step 2: the residue field of `S` is `L`, via the bijective structure map.
  have hres : Function.Bijective
      (fun c : L => Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥S) (algebraMap L ↥S c)) :=
    Work.MotC2.InfPlaceCore.residue_field E
  let e : L ≃ₐ[L] (↥S ⧸ IsLocalRing.maximalIdeal ↥S) :=
    AlgEquiv.ofBijective ((Ideal.Quotient.mkₐ L (IsLocalRing.maximalIdeal ↥S)).comp
      (Algebra.ofId L ↥S)) hres
  let zbar : ↥S ⧸ IsLocalRing.maximalIdeal ↥S :=
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥S) ⟨z, hzS⟩
  let c : L := e.symm zbar
  -- Step 3: reduce `Q := minpoly L z` modulo the maximal ideal of `S`.  Each of the three
  -- displayed identities is `Polynomial.aeval_algHom_apply` (an algebra homomorphism commutes
  -- with `aeval`).
  have hQaeval : aeval (⟨z, hzS⟩ : ↥S) (minpoly L z) = 0 := by
    apply Subtype.ext
    have h1 := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom L ↥S
      (WeierstrassCurve.Affine.FunctionField E)) (⟨z, hzS⟩ : ↥S) (minpoly L z)
    have h2 : aeval z (minpoly L z) = 0 := minpoly.aeval L z
    simpa using h1.trans h2
  have hQbar : aeval zbar (minpoly L z) = 0 := by
    have h1 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ L (IsLocalRing.maximalIdeal ↥S))
      (⟨z, hzS⟩ : ↥S) (minpoly L z)
    rw [hQaeval, map_zero] at h1
    simpa using h1
  have hQc : aeval c (minpoly L z) = 0 := by
    have h1 := Polynomial.aeval_algHom_apply e.symm.toAlgHom zbar (minpoly L z)
    rw [hQbar, map_zero] at h1
    simpa using h1
  -- Step 4: `c` is a root in `L` of the minimal polynomial of `z`; since `z` is integral and
  -- `minpoly L z` is irreducible, `minpoly.root` then gives `algebraMap L L(E) c = z`.
  have hroot : (minpoly L z).IsRoot c := by
    simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hQc
  exact ⟨c, (minpoly.root hz.isIntegral hroot).symm⟩

end Work.MotK

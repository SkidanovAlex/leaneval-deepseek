import Mathlib
import Submission.Work.Totaro.Defs
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

/-- **A `Variety` instance on `X × 𝔸ⁿ` with the *canonical* structure morphism.**

`Work.Totaro.prodOver 𝕜 X (AffineN 𝕜 n)` is the fibre product `pullback (X ↘ Spec 𝕜) (𝔸ⁿ ↘ Spec 𝕜)`
and carries the canonical structure morphism `pullback.fst ≫ (X ↘ Spec 𝕜)` to `Spec 𝕜` (this is
`Work.K3.prodOverOver`, an instance).  `Work.K3Inputs.exists_variety_prodOver_affineSpace` proves the
existence of a `Variety 𝕜` instance on it, but with an *unspecified* structure morphism, whereas the
associativity isomorphisms of the exponents (`Work.K3Inputs.prodOver_affine_assoc`) and the exponent
shift `Work.Totaro.partialIso_prod_affine` (proved from it) refer to the canonical one; the present
result provides the instance *with that canonical structure morphism*, which makes the types of those
two families of results agree.

The proof is the construction of `Work.K3Inputs.exists_variety_prodOver_affineSpace` with
`«over» := Work.K3.prodOverOver X (AffineN 𝕜 n)`: integrality of the fibre product from the
geometric integrality of affine space over `𝕜` (Mathlib's
`AlgebraicGeometry.AffineSpace.geometricallyIntegral` and
`GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`), and separatedness / local finiteness of
type / quasi-compactness as base changes of `X ↘ Spec 𝕜`. -/
theorem prodOver_affineSpace_canonical_variety {𝕜 : Type} [Field 𝕜]
    (X : AlgebraicGeometry.Scheme.{0}) [MotivicInvariants.Variety 𝕜 X] (n : ℕ) :
    ∃ v : MotivicInvariants.Variety 𝕜
        (Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 n)),
      v.over = Work.K3.prodOverOver X (Work.Totaro.AffineN 𝕜 n) := by
  -- The four `Variety` fields of `X`, which are not registered as instances.
  haveI hXlf : LocallyOfFiniteType (X ↘ Spec (.of 𝕜)) :=
    Work.K3Inputs.locallyOfFiniteType_of_variety 𝕜 X
  haveI hXn : IsLocallyNoetherian X := Work.K3Inputs.isLocallyNoetherian_of_variety 𝕜 X
  haveI hXs : IsSeparated (X ↘ Spec (.of 𝕜)) :=
    (inferInstance : MotivicInvariants.Variety 𝕜 X).isSeparated
  haveI hXq : QuasiCompact (X ↘ Spec (.of 𝕜)) :=
    (inferInstance : MotivicInvariants.Variety 𝕜 X).quasicompact
  -- The affine factor: geometrically integral, and locally of finite type (`Variety 𝕜 𝔸ⁿ`).
  haveI hAg : GeometricallyIntegral (Work.Totaro.AffineN 𝕜 n ↘ Spec (.of 𝕜)) :=
    Work.K3Inputs.geometricallyIntegral_affineN 𝕜 n
  haveI hAl : LocallyOfFiniteType (Work.Totaro.AffineN 𝕜 n ↘ Spec (.of 𝕜)) :=
    (inferInstance : MotivicInvariants.Variety 𝕜 (Work.Totaro.AffineN 𝕜 n)).locallyOfFiniteType
  -- Integrality of the fibre product: `𝔸ⁿ → Spec 𝕜` is geometrically integral, flat and
  -- universally open, and `X` is integral and locally noetherian.
  haveI hZi : IsIntegral (Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 n)) := by
    show IsIntegral
      (Limits.pullback (X ↘ Spec (.of 𝕜)) (Work.Totaro.AffineN 𝕜 n ↘ Spec (.of 𝕜)))
    infer_instance
  -- The remaining three fields: base change of `X ↘ Spec 𝕜` along `𝔸ⁿ ↘ Spec 𝕜`.
  haveI hZs : IsSeparated
      (Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 n) ↘ Spec (.of 𝕜)) := by
    show IsSeparated (Limits.pullback.fst (X ↘ Spec (.of 𝕜))
      (Work.Totaro.AffineN 𝕜 n ↘ Spec (.of 𝕜)) ≫ (X ↘ Spec (.of 𝕜)))
    infer_instance
  haveI hZlf : LocallyOfFiniteType
      (Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 n) ↘ Spec (.of 𝕜)) := by
    show LocallyOfFiniteType (Limits.pullback.fst (X ↘ Spec (.of 𝕜))
      (Work.Totaro.AffineN 𝕜 n ↘ Spec (.of 𝕜)) ≫ (X ↘ Spec (.of 𝕜)))
    infer_instance
  haveI hZq : QuasiCompact
      (Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 n) ↘ Spec (.of 𝕜)) := by
    show QuasiCompact (Limits.pullback.fst (X ↘ Spec (.of 𝕜))
      (Work.Totaro.AffineN 𝕜 n ↘ Spec (.of 𝕜)) ≫ (X ↘ Spec (.of 𝕜)))
    infer_instance
  -- The record, with the structure morphism pinned to the canonical `Work.K3.prodOverOver`.
  refine ⟨{ «over» := Work.K3.prodOverOver X (Work.Totaro.AffineN 𝕜 n),
            isIntegral := hZi, isSeparated := hZs, locallyOfFiniteType := hZlf,
            quasicompact := hZq }, rfl⟩

end

end Work.Totaro

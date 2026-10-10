import Submission.Work.CY3Stab.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Variety` — the cylinder of a variety is a variety

`Work.K3Inputs.exists_variety_prodOver_affineSpace` provides the `Variety` structure on the product
`X × 𝔸ⁿ` taken in the order of `Work.K3.prodOver` (the `X`-leg first).  The cylinder
`Work.CY3Stab.WProd X k` is the *base change* of `X` along `𝔸ᵏ ⟶ Spec 𝕜`, i.e. the same fibred
product with the two legs exchanged (so that the analysed base-change lemmas of the K3 chapter
apply verbatim); this file records the corresponding `Variety` statement for that order.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The variety structure on the cylinder**, *as a plain definition* (not via
`Classical.choice` of an existential): its `over` field is `Work.CY3Stab.wProdOver`, i.e. the
canonical structure morphism `𝔸ᵏ × X ⟶ 𝔸ᵏ ⟶ Spec 𝕜`.  This matters for every statement whose
*type* mentions the structure morphism of the cylinder (e.g. `Work.CY3.StronglyBirational`): the
`over` field of `Classical.choice (exists_variety_wProd …)` is opaque (`Classical.choice` has no
reduction rule), whereas `(varietyWProd X k).over` reduces definitionally to `wProdOver X k`. -/
noncomputable def varietyWProd (X : Scheme.{0}) [Variety 𝕜 X] (k : ℕ) :
    Variety 𝕜 (WProd (𝕜 := 𝕜) X k) := by
  haveI hXlf : LocallyOfFiniteType (X ↘ Spec (.of 𝕜)) :=
    Work.K3Inputs.locallyOfFiniteType_of_variety 𝕜 X
  haveI hXn : IsLocallyNoetherian X := Work.K3Inputs.isLocallyNoetherian_of_variety 𝕜 X
  haveI hXs : IsSeparated (X ↘ Spec (.of 𝕜)) := (inferInstance : Variety 𝕜 X).isSeparated
  haveI hXq : QuasiCompact (X ↘ Spec (.of 𝕜)) := (inferInstance : Variety 𝕜 X).quasicompact
  haveI hAg : GeometricallyIntegral (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) :=
    Work.K3Inputs.geometricallyIntegral_affineN 𝕜 k
  haveI hAl : LocallyOfFiniteType (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) :=
    (inferInstance : Variety 𝕜 (AffineK (𝕜 := 𝕜) k)).locallyOfFiniteType
  haveI hZi : IsIntegral (WProd (𝕜 := 𝕜) X k) := by
    show IsIntegral (Limits.pullback (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜)))
    infer_instance
  haveI hZs : IsSeparated ((wProdOver (𝕜 := 𝕜) X k).1) :=
    inferInstanceAs (IsSeparated (Limits.pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))
      (X ↘ Spec (.of 𝕜)) ≫ (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))))
  haveI hZlf : LocallyOfFiniteType ((wProdOver (𝕜 := 𝕜) X k).1) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))
      (X ↘ Spec (.of 𝕜)) ≫ (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))))
  haveI hZq : QuasiCompact ((wProdOver (𝕜 := 𝕜) X k).1) :=
    inferInstanceAs (QuasiCompact (Limits.pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))
      (X ↘ Spec (.of 𝕜)) ≫ (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))))
  have hVar : Variety 𝕜 (WProd (𝕜 := 𝕜) X k) :=
    { «over» := wProdOver (𝕜 := 𝕜) X k, isIntegral := hZi,
      isSeparated := hZs, locallyOfFiniteType := hZlf, quasicompact := hZq }
  exact hVar

/-- **The cylinder of a variety is a variety.**

`𝔸ᵏ × X` is integral (the affine factor is geometrically integral and flat, and `X` is integral
and locally noetherian), and separated / quasi-compact / locally of finite type as a base change of
`X ⟶ Spec 𝕜`.  Stated as `Nonempty` because `Variety` is data; a caller installs the instance with
`letI := Classical.choice (exists_variety_wProd 𝕜 X k)`. -/
theorem exists_variety_wProd (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X] (k : ℕ) :
    Nonempty (Variety 𝕜 (WProd (𝕜 := 𝕜) X k)) := by
  haveI hXlf : LocallyOfFiniteType (X ↘ Spec (.of 𝕜)) :=
    Work.K3Inputs.locallyOfFiniteType_of_variety 𝕜 X
  haveI hXn : IsLocallyNoetherian X := Work.K3Inputs.isLocallyNoetherian_of_variety 𝕜 X
  haveI hXs : IsSeparated (X ↘ Spec (.of 𝕜)) := (inferInstance : Variety 𝕜 X).isSeparated
  haveI hXq : QuasiCompact (X ↘ Spec (.of 𝕜)) := (inferInstance : Variety 𝕜 X).quasicompact
  haveI hAg : GeometricallyIntegral (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) :=
    Work.K3Inputs.geometricallyIntegral_affineN 𝕜 k
  haveI hAl : LocallyOfFiniteType (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) :=
    (inferInstance : Variety 𝕜 (AffineK (𝕜 := 𝕜) k)).locallyOfFiniteType
  haveI hZi : IsIntegral (WProd (𝕜 := 𝕜) X k) := by
    show IsIntegral (Limits.pullback (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜)))
    infer_instance
  haveI hZs : IsSeparated ((wProdOver (𝕜 := 𝕜) X k).1) :=
    inferInstanceAs (IsSeparated (Limits.pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))
      (X ↘ Spec (.of 𝕜)) ≫ (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))))
  haveI hZlf : LocallyOfFiniteType ((wProdOver (𝕜 := 𝕜) X k).1) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))
      (X ↘ Spec (.of 𝕜)) ≫ (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))))
  haveI hZq : QuasiCompact ((wProdOver (𝕜 := 𝕜) X k).1) :=
    inferInstanceAs (QuasiCompact (Limits.pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))
      (X ↘ Spec (.of 𝕜)) ≫ (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))))
  haveI hVar : Variety 𝕜 (WProd (𝕜 := 𝕜) X k) :=
    { «over» := wProdOver (𝕜 := 𝕜) X k, isIntegral := hZi,
      isSeparated := hZs, locallyOfFiniteType := hZlf, quasicompact := hZq }
  exact ⟨hVar⟩

end

end Work.CY3Stab

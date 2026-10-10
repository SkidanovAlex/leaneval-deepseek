import Mathlib
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

/-! ## Two facts about `𝔸ⁿ` and about varieties that typeclass search misses

Both are consequences of *existing* Mathlib instances; the point of the lemmas is to make them
reachable.  The `OverClass` instance of `𝔸(n; S) ⟶ S` that typeclass search finds is
`Variety.over` (the affine space is a variety, and `Variety.over` is `instance_reducible`), and
the term it produces is not syntactically the canonical one recorded in the discrimination tree
of the `AffineSpace` instances.  Writing the goal in the canonical form recovers them. -/

/-- **Affine space is geometrically integral over the base.**  This is Mathlib's
`AlgebraicGeometry.AffineSpace.geometricallyIntegral`, restated for the structure morphism that
typeclass search actually produces. -/
lemma geometricallyIntegral_affineN (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    GeometricallyIntegral (AffineN 𝕜 n ↘ Spec (.of 𝕜)) := by
  change GeometricallyIntegral (CategoryTheory.over (AffineN 𝕜 n) (Spec (.of 𝕜))
    (CanonicallyOverClass.toOverClass (X := AffineN 𝕜 n) (S := Spec (.of 𝕜))))
  infer_instance

/-- The structure morphism of a variety is locally of finite type (a field of `Variety`). -/
lemma locallyOfFiniteType_of_variety (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [MotivicInvariants.Variety 𝕜 X] : LocallyOfFiniteType (X ↘ Spec (.of 𝕜)) :=
  (inferInstance : MotivicInvariants.Variety 𝕜 X).locallyOfFiniteType

/-- A variety over a field is locally noetherian: it is locally of finite type over `Spec 𝕜`,
which is locally noetherian.  (A field is a noetherian ring.) -/
lemma isLocallyNoetherian_of_variety (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [MotivicInvariants.Variety 𝕜 X] : IsLocallyNoetherian X := by
  haveI := locallyOfFiniteType_of_variety 𝕜 X
  exact LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of 𝕜))

/-- **The product of a variety with affine space is a variety.**

`X × 𝔸ⁿ` over `Spec 𝕜` is integral (`𝔸ⁿ ⟶ Spec 𝕜` is geometrically integral and flat, so
Mathlib's `AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` applies,
using that `X` is integral and locally noetherian), and separated / quasi-compact / locally of
finite type as a base change of `X ⟶ Spec 𝕜`.  This is the instance that the *existential* in
`Work.K3.StablyBirational` (which binds a `Variety` instance for each product) requires in order
for `Work.K3Inputs.StablyBirat` to be transferred to it; note that a product of two `𝕜`-varieties
need not be a variety, so the geometric integrality of the affine factor is genuinely used.

Stated as a proposition (`Nonempty`) because `Variety` is data; a caller installs the instance
with `letI := Classical.choice (exists_variety_prodOver_affineSpace 𝕜 X n)`. -/
theorem exists_variety_prodOver_affineSpace (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [MotivicInvariants.Variety 𝕜 X] (n : ℕ) :
    Nonempty (MotivicInvariants.Variety 𝕜 (Work.K3.prodOver 𝕜 X (Work.K3Inputs.AffineN 𝕜 n))) := by
  -- The four `Variety` fields of `X`, which are not registered as instances.
  haveI hXlf : LocallyOfFiniteType (X ↘ Spec (.of 𝕜)) := locallyOfFiniteType_of_variety 𝕜 X
  haveI hXn : IsLocallyNoetherian X := isLocallyNoetherian_of_variety 𝕜 X
  haveI hXs : IsSeparated (X ↘ Spec (.of 𝕜)) :=
    (inferInstance : MotivicInvariants.Variety 𝕜 X).isSeparated
  haveI hXq : QuasiCompact (X ↘ Spec (.of 𝕜)) :=
    (inferInstance : MotivicInvariants.Variety 𝕜 X).quasicompact
  -- The affine factor: geometrically integral, and locally of finite type (from `Variety 𝕜 𝔸ⁿ`).
  haveI hAg : GeometricallyIntegral (AffineN 𝕜 n ↘ Spec (.of 𝕜)) := geometricallyIntegral_affineN 𝕜 n
  haveI hAl : LocallyOfFiniteType (AffineN 𝕜 n ↘ Spec (.of 𝕜)) :=
    (inferInstance : MotivicInvariants.Variety 𝕜 (AffineN 𝕜 n)).locallyOfFiniteType
  -- Integrality: `𝔸ⁿ → Spec 𝕜` is geometrically integral, flat and universally open, and
  -- `X` is integral and locally noetherian, so `X × 𝔸ⁿ` is integral.
  haveI hZi : IsIntegral (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n)) := by
    show IsIntegral (Limits.pullback (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 n ↘ Spec (.of 𝕜)))
    infer_instance
  -- The remaining three fields: base change of `X ↘ Spec 𝕜` along `𝔸ⁿ ↘ Spec 𝕜`.
  haveI hZs : IsSeparated (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) ↘ Spec (.of 𝕜)) := by
    show IsSeparated (Limits.pullback.fst (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 n ↘ Spec (.of 𝕜)) ≫
      (X ↘ Spec (.of 𝕜)))
    infer_instance
  haveI hZlf : LocallyOfFiniteType (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) ↘ Spec (.of 𝕜)) := by
    show LocallyOfFiniteType (Limits.pullback.fst (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 n ↘ Spec (.of 𝕜)) ≫
      (X ↘ Spec (.of 𝕜)))
    infer_instance
  haveI hZq : QuasiCompact (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) ↘ Spec (.of 𝕜)) := by
    show QuasiCompact (Limits.pullback.fst (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 n ↘ Spec (.of 𝕜)) ≫
      (X ↘ Spec (.of 𝕜)))
    infer_instance
  haveI hVar : MotivicInvariants.Variety 𝕜 (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n)) :=
    { «over» := inferInstance, isIntegral := inferInstance,
      isSeparated := inferInstance, locallyOfFiniteType := inferInstance,
      quasicompact := inferInstance }
  exact ⟨hVar⟩

end

end Work.K3Inputs

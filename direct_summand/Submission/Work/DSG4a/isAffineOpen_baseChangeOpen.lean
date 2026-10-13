import Mathlib
import Submission.Work.DSG4a.BaseChange

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits
universe u
-- `baseChangeOpen X f (U i)` is the preimage of `U i` under the base-change projection
-- `pullback.fst f (specAlgebraMap A A')` (see Submission/Work/DSG4a/BaseChange.lean). That
-- projection is the base change of the affine morphism `Spec A' ⟶ Spec A`, hence affine
-- (`isAffineHom_isStableUnderBaseChange` with `IsPullback.of_hasPullback f _`), and
-- `IsAffineOpen.preimage` gives the claim. Reviewer advice: `IsAffineHom (pullback.fst _ _)`
-- is not found by `inferInstance`, it has to be built with
-- `MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f _).flip`.
theorem isAffineOpen_baseChangeOpen {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (i : ι) :
    AlgebraicGeometry.IsAffineOpen (Work.DSG4a.baseChangeOpen (A := A) (A' := A') X f (U i)) := by
  -- The base-change projection `X_{A'} ⟶ X` is the base change of the affine morphism
  -- `Spec A' ⟶ Spec A`, hence affine.
  haveI : IsAffineHom (Work.DSG4a.specAlgebraMap (A := A) (A' := A')) := inferInstance
  haveI : IsAffineHom (pullback.fst f (Work.DSG4a.specAlgebraMap (A := A) (A' := A'))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (Work.DSG4a.specAlgebraMap (A := A) (A' := A'))).flip
      (inferInstance : IsAffineHom _)
  exact (hU i).preimage _

end Work.DSG4a

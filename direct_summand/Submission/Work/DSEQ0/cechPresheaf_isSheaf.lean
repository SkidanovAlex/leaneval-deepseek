import Mathlib
import Submission.Work.DSMap.Map

namespace Work.DSEQ0

open CategoryTheory

universe a

/-- The presheaf of `A`-modules `U ↦ Γ(X,U)` (with the `A`-module structure induced by
`f : X ⟶ Spec A`) is a sheaf.

This is the structure sheaf of `X` with the `A`-module structure restricted along `f`; the
underlying presheaf of types is literally that of `X.presheaf`, so the sheaf condition is
inherited from the structure sheaf via the forgetful functors. -/
theorem cechPresheaf_isSheaf (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) :
    TopCat.Presheaf.IsSheaf (DSMap.cechPresheaf A X f) := by
  -- The structure sheaf of `X`, with its ring structure forgotten, is a sheaf of types.
  have hR : TopCat.Presheaf.IsSheaf (X.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget CommRingCat)
      X.presheaf).mp X.IsSheaf
  -- The underlying presheaf of types of `cechPresheaf` *is* that of the structure sheaf.
  have hM : TopCat.Presheaf.IsSheaf
      (DSMap.cechPresheaf A X f ⋙ CategoryTheory.forget (ModuleCat A)) := by
    rw [show (DSMap.cechPresheaf A X f ⋙ CategoryTheory.forget (ModuleCat A)) =
        (X.presheaf ⋙ CategoryTheory.forget CommRingCat) from rfl]
    exact hR
  -- Check the sheaf condition on the underlying presheaf of types.
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget (ModuleCat A))
    (DSMap.cechPresheaf A X f)).mpr hM

end Work.DSEQ0

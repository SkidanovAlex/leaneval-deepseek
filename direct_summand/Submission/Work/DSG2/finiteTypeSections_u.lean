import Mathlib
import Submission.Work.DSG2.Defs

/-!
# DSG2: sections over an affine open are a finitely generated algebra

If `f : X ⟶ Spec A` is locally of finite type and `U ⊆ X` is affine open, then the
`A`-algebra `Γ(X, U)` (for the structure map `Work.DSG2.sectionAlgebra f U`) is finitely
generated.

This is essentially the definition of `LocallyOfFiniteType` (`Scheme.Hom.finiteType_appLE`,
which gives finite-typeness of `f.appLE ⊤ U le_top`) combined with the fact that the canonical
isomorphism `Γ(Spec A) ≅ A` is a surjective — hence finite-type — ring homomorphism, and the
stability of `RingHom.FiniteType` under composition.
-/

open CategoryTheory AlgebraicGeometry

namespace Work.DSG2

theorem finiteTypeSections_u {A : Type*} [CommRing A] {X : AlgebraicGeometry.Scheme}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.LocallyOfFiniteType f]
    (U : X.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    (Work.DSG2.sectionAlgebra f U).FiniteType := by
  -- `LocallyOfFiniteType` is defined by the finite-typeness of `appLE` on affine opens,
  -- so the statement is this definition instantiated at `⊤ ⊆ Spec A` and `U`.
  have h : (f.appLE ⊤ U le_top).hom.FiniteType :=
    Scheme.Hom.finiteType_appLE f (isAffineOpen_top (Spec (CommRingCat.of A))) hU le_top
  -- `Γ(Spec A) ≅ A` is (in the direction `A → Γ(Spec A)`) a surjection, hence of finite type.
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      ((Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective)
  -- `sectionAlgebra f U` is by definition the composite of these two ring homomorphisms.
  exact h.comp h2

end Work.DSG2

import Mathlib
import Submission.Work.SSGRoute.ExtendFunctorIso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary definitions for `Work.SSGRoute.mapExtAddHom_extMk`

The chain map `φ : R'.complex ⟶ F(R.complex)` (with its augmentation compatibility) induces a
cochain map `phiSharp F R R' φ : R'.cochainComplex ⟶ F(R.cochainComplex)` on the `ℤ`-indexed
cochain complexes, by extension along `ComplexShape.embeddingDownNat` and the canonical
commutation `extendFunctorIso` of `F` with `extend`.
-/

open CategoryTheory Limits

namespace Work.SSGRoute

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category D] [Abelian D]

/-- The cochain map on `ℤ`-indexed complexes induced by a chain map `φ` into `F(R.complex)`. -/
noncomputable def phiSharp (F : C ⥤ D) [F.Additive] {X : C} (R : ProjectiveResolution X)
    {X' : D} (R' : ProjectiveResolution X')
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex) :
    R'.cochainComplex ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex :=
  HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat ≫
    (extendFunctorIso F R.complex).hom



open CategoryTheory.Limits in
/-- The degree-`n` morphism of cochain complexes `R.cochainComplex ⟶ single Y ⟦n⟧` whose
`equivHomShift`-image is the cocycle defining `R.extMk g`. -/
noncomputable def extMkShiftedHom {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (R : ProjectiveResolution X) {n : ℕ}
    (g : R.complex.X n ⟶ Y) (hg : R.complex.d (n + 1) n ≫ g = 0) :
    CategoryTheory.ShiftedHom R.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) ((n : ℤ)) :=
  CochainComplex.HomComplex.Cocycle.equivHomShift.symm
    (CochainComplex.HomComplex.Cocycle.toSingleMk
      ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g) (by simp) (-↑(n+1)) (by lia)
      (by simpa [R.cochainComplex_d (-(↑n+1)) (-↑n) (n+1) n (by simp) rfl, hg]))

end Work.SSGRoute

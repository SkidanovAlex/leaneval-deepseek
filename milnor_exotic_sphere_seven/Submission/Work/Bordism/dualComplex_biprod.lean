import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.homology_biprod_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dual complex of a biproduct of chain complexes

`Work.Cohomology.dualComplex R C` is the `R`-dual cochain complex of a chain complex `C` of
`R`-modules.  Dualising is a contravariant *additive* functor, and an additive functor carries
finite biproducts to finite biproducts (Mathlib's `Functor.mapBiprod`).  This file packages that
functor (`dualComplexFunctor`), proves that it is additive, and concludes

`dualComplex R (C ⊞ D) ≅ dualComplex R C ⊞ dualComplex R D`
(`dualComplex_biprod`).

The additivity is exactly the statement that the transpose of a sum of chain maps is the sum of
the transposes (`dualComplexMap_add'`), which is reduced to its degreewise linear-algebra content.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace Work.Bordism

noncomputable section

/-- The transpose of a sum of linear maps is the sum of the transposes. -/
lemma dualMap_add' (R : Type) [CommRing R] {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f g : M →ₗ[R] N) :
    (f + g).dualMap = f.dualMap + g.dualMap := by
  ext φ x
  simp

/-- The `n`-th component of the dual of a sum of chain maps is the sum of the components. -/
lemma dualComplexMapComp_add' (R : Type) [CommRing R] (C D : ChainComplex (ModuleCat R) ℕ)
    (f g : C ⟶ D) (n : ℕ) :
    Work.Cohomology.dualComplexMapComp R C D (f + g) n
      = Work.Cohomology.dualComplexMapComp R C D f n
        + Work.Cohomology.dualComplexMapComp R C D g n := by
  apply ModuleCat.hom_ext
  show ((f + g).f n).hom.dualMap = (f.f n).hom.dualMap + (g.f n).hom.dualMap
  rw [HomologicalComplex.add_f_apply]
  rw [show (f.f n + g.f n).hom = (f.f n).hom + (g.f n).hom from rfl]
  exact dualMap_add' R _ _

/-- The dual of a sum of chain maps is the sum of the duals. -/
lemma dualComplexMap_add' (R : Type) [CommRing R] (C D : ChainComplex (ModuleCat R) ℕ)
    (f g : C ⟶ D) :
    Work.Cohomology.dualComplexMap R C D (f + g)
      = Work.Cohomology.dualComplexMap R C D f
        + Work.Cohomology.dualComplexMap R C D g := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.add_f_apply, Work.Cohomology.dualComplexMap_f,
    Work.Cohomology.dualComplexMap_f, Work.Cohomology.dualComplexMap_f]
  exact dualComplexMapComp_add' R C D f g n

/-- **The dual cochain complex, as a contravariant functor** on chain complexes of `R`-modules:
a chain map `f : C ⟶ D` is sent to the transposed cochain map `dualComplex D ⟶ dualComplex C`. -/
def dualComplexFunctor (R : Type) [CommRing R] :
    (ChainComplex (ModuleCat R) ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat R) ℕ where
  obj X := Work.Cohomology.dualComplex R X.unop
  map {X Y} f := Work.Cohomology.dualComplexMap R Y.unop X.unop f.unop
  map_id X := by
    rw [unop_id, Work.Cohomology.dualComplexMap_id]
  map_comp {X Y Z} f g := by
    rw [unop_comp, Work.Cohomology.dualComplexMap_comp]

/-- The dual complex functor is additive. -/
instance dualComplexFunctor_additive (R : Type) [CommRing R] :
    (dualComplexFunctor R).Additive where
  map_add {X Y} f g := by
    show Work.Cohomology.dualComplexMap R Y.unop X.unop (f + g).unop
      = Work.Cohomology.dualComplexMap R Y.unop X.unop f.unop
        + Work.Cohomology.dualComplexMap R Y.unop X.unop g.unop
    rw [unop_add, dualComplexMap_add']

set_option linter.style.haveILetI false in
/-- The dual of a biproduct of chain complexes of `ℤ`-modules is the biproduct of the duals. -/
theorem dualComplex_biprod (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    Nonempty (Work.Cohomology.dualComplex ℤ (C ⊞ D) ≅
      (Work.Cohomology.dualComplex ℤ C ⊞ Work.Cohomology.dualComplex ℤ D)) := by
  -- `dualComplexFunctor` is additive, hence preserves the binary biproduct
  haveI : PreservesBinaryBiproduct (Opposite.op C) (Opposite.op D) (dualComplexFunctor ℤ) :=
    preservesBinaryBiproduct_of_preservesBiproduct (dualComplexFunctor ℤ) _ _
  -- `op (C ⊞ D) ≅ op C ⊞ op D`, and `mapBiprod` identifies the image of a biproduct
  exact ⟨(dualComplexFunctor ℤ).mapIso (biprod.opIso C D) ≪≫
    (dualComplexFunctor ℤ).mapBiprod (Opposite.op C) (Opposite.op D)⟩

end

end Work.Bordism

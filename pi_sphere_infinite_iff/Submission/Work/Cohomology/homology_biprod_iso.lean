import Mathlib
import Submission.Work.Cohomology.Singular

namespace Work.Cohomology

open CategoryTheory Limits

set_option linter.style.haveILetI false in
/-- The homology of a biproduct of cochain complexes of `ℤ`-modules is the biproduct of the
homologies, compatibly with the biproduct structure maps. -/
theorem homology_biprod_iso (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    ∃ (e : (C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k),
      (biprod.inl : C.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
        = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k ∧
      (biprod.inr : D.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
        = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k := by
  -- The `k`-th homology is an additive functor on the (abelian) category of cochain complexes;
  -- additive functors preserve finite biproducts, so it carries the biproduct `C ⊞ D` to the
  -- biproduct `C.homology k ⊞ D.homology k`. Its structure maps are `homologyMap` of the
  -- structure maps of the biproduct of complexes, which gives exactly the stated compatibility.
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  refine ⟨F.mapBiprod C D, ?_, ?_⟩
  · erw [Functor.mapBiprod_inv, biprod.inl_desc]
    rfl
  · erw [Functor.mapBiprod_inv, biprod.inr_desc]
    rfl

end Work.Cohomology

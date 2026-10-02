import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.cokernelComponent
import Submission.Work.Kunneth.TopCat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Setup for the relative Eilenberg–Zilber homology isomorphism

The target `Work.Serre.relEZ_homology_iso` states that for a space `W` and a pair `(P,Q)` the
tensor product complex `C_*(W) ⊗_ℤ C_*(P,Q)` (built with the Koszul tensor product
`Work.Kunneth.tpC`) has the same homology as the relative chain complex of the product pair
`(W × P, W × Q)`.

This file collects the vocabulary of that statement:

* `Work.Serre.tpFunctor C` — the endofunctor `D ↦ tpC C D` of the category of chain complexes of
  `ℤ`-modules (with `Work.Kunneth.tpMap C C 𝟙 -` on morphisms), which is the functor whose
  exactness (for `C` degreewise flat) is the content of the relative Eilenberg–Zilber theorem;
* `Work.Serre.tpMap_zero_left` — `tpMap C C (𝟙 C) 0 = 0`, so that `tpFunctor C` preserves zero
  morphisms.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- `Work.Kunneth.tpMap C C (𝟙 C)` kills the zero morphism. -/
theorem tpMap_zero_left (C D D' : ChainComplex (ModuleCat ℤ) ℕ) :
    Work.Kunneth.tpMap C C D D' (𝟙 C) (0 : D ⟶ D') = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  show ModuleCat.ofHom (Work.Kunneth.tpMapLin C C D D' (𝟙 C) 0 n) = 0
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom]
  show Work.Kunneth.tpMapLin C C D D' (𝟙 C) 0 n = 0
  apply DirectSum.linearMap_ext ℤ
  intro pq
  apply LinearMap.ext
  intro z
  simp only [Work.Kunneth.tpMapLin, LinearMap.comp_apply, DirectSum.toModule_lof,
    HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply,
    TensorProduct.map_zero_right, map_zero]
  exact map_zero _

/-- **The functor `D ↦ tpC C D`** of tensoring a chain complex (of `ℤ`-modules) on the left by
the fixed complex `C`, with `Work.Kunneth.tpMap C C (𝟙 C) -` on morphisms. -/
def tpFunctor (C : ChainComplex (ModuleCat ℤ) ℕ) :
    ChainComplex (ModuleCat ℤ) ℕ ⥤ ChainComplex (ModuleCat ℤ) ℕ where
  obj D := Work.Kunneth.tpC C D
  map {D D'} f := Work.Kunneth.tpMap C C D D' (𝟙 C) f
  map_id D := Work.Kunneth.tpMap_id C D
  map_comp {D D' D''} f g := by
    rw [Work.Kunneth.tpMap_comp, Category.id_comp]

@[simp]
theorem tpFunctor_obj (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    (tpFunctor C).obj D = Work.Kunneth.tpC C D := rfl

/-- The value of `tpFunctor C` on a morphism. -/
theorem tpFunctor_map (C D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : D ⟶ D') :
    (tpFunctor C).map f = Work.Kunneth.tpMap C C D D' (𝟙 C) f := rfl

instance (C : ChainComplex (ModuleCat ℤ) ℕ) : (tpFunctor C).PreservesZeroMorphisms where
  map_zero := fun _ _ => tpMap_zero_left C _ _

end

end Work.Serre

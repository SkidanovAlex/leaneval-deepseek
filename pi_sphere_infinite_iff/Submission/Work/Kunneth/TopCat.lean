import Mathlib
import Submission.Work.Kunneth.AW
import Submission.Work.Kunneth.EZMap
import Submission.Work.Kunneth.aw_ez_homotopy
import Submission.Work.Kunneth.ez_aw_homotopy

/-!
# The Alexander–Whitney and Eilenberg–Zilber maps for topological spaces

The chain-level Eilenberg–Zilber data of this chapter is stated for simplicial sets.  For
topological spaces one uses the singular simplicial set functor `TopCat.toSSet`, which is a
monoidal functor for the cartesian structures (`TopCat.toSSet.Monoidal`, from Mathlib's
`TopCat.toSSetType`), so that `Sing (X ⊗ Y) ≅ Sing X ⊗ Sing Y`.  Transporting along that
isomorphism gives

* `Work.Kunneth.singProdIso X Y : Sing (X ⊗ Y) ≅ Sing X ⊗ Sing Y`;
* `Work.Kunneth.awMapT X Y` — the **Alexander–Whitney chain map**
  `C_*(X × Y) ⟶ C_*(X) ⊗_ℤ C_*(Y)` for topological spaces `X`, `Y`;
* `Work.Kunneth.ezMapT X Y` — the **Eilenberg–Zilber shuffle chain map** in the reverse
  direction.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The canonical isomorphism `Sing (X ⊗ Y) ≅ Sing X ⊗ Sing Y` for topological spaces. -/
def singProdIso (X Y : TopCat) :
    TopCat.toSSet.obj (X ⊗ Y) ≅ TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y :=
  (Functor.Monoidal.μIso TopCat.toSSet X Y).symm

/-- **The Alexander–Whitney chain map for topological spaces**:
`C_*(X × Y) ⟶ C_*(X) ⊗_ℤ C_*(Y)`. -/
def awMapT (X Y : TopCat) :
    sChain (TopCat.toSSet.obj (X ⊗ Y)) ⟶ tChain (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) :=
  SSet.chainComplexMap (singProdIso X Y).hom zz ≫
    awMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)

/-- **The Eilenberg–Zilber shuffle chain map for topological spaces**:
`C_*(X) ⊗_ℤ C_*(Y) ⟶ C_*(X × Y)`. -/
def ezMapT (X Y : TopCat) :
    tChain (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ⟶ sChain (TopCat.toSSet.obj (X ⊗ Y)) :=
  ezMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ≫
    SSet.chainComplexMap (singProdIso X Y).inv zz

/-- The two transports are inverse: `Sing (X ⊗ Y) ≅ Sing X ⊗ Sing Y` induces mutually inverse
chain maps. -/
theorem chainComplexMap_singProdIso_comp (X Y : TopCat) :
    CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (singProdIso X Y).hom zz)
        (SSet.chainComplexMap (singProdIso X Y).inv zz)
      = CategoryTheory.CategoryStruct.id
          (sChain (TopCat.toSSet.obj (X ⊗ Y))) := by
  rw [← Functor.map_comp, Iso.hom_inv_id]
  exact CategoryTheory.Functor.map_id _ _

/-- The homotopy `EZ ∘ AW ≃ id` for topological spaces, transported from the simplicial
statement `Work.Kunneth.aw_ez_homotopy`. -/
theorem aw_ez_homotopyT (X Y : TopCat) :
    Nonempty (Homotopy
      (CategoryTheory.CategoryStruct.comp (awMapT X Y) (ezMapT X Y))
      (CategoryTheory.CategoryStruct.id (sChain (TopCat.toSSet.obj (X ⊗ Y))))) := by
  obtain ⟨H⟩ := aw_ez_homotopy (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
  refine ⟨(Homotopy.ofEq (CategoryTheory.Category.assoc _ _ _) |>.symm.trans
      ((H.compLeft (SSet.chainComplexMap (singProdIso X Y).hom zz)).compRight
        (SSet.chainComplexMap (singProdIso X Y).inv zz)) |>.trans
      (Homotopy.ofEq ?_))⟩
  simp only [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp,
    chainComplexMap_singProdIso_comp]

end

end Work.Kunneth

import Mathlib
import Submission.Work.Kunneth.TopCat
import Submission.Work.Kunneth.ez_aw_homotopy

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The second Eilenberg–Zilber homotopy for topological spaces

The predecessor file `Submission/Work/Kunneth/TopCat.lean` transports the simplicial homotopy
`aw_ez_homotopy` to topological spaces, proving that `awMapT ≫ ezMapT ≃ 𝟙` on `C_*(X × Y)`.

Here we transport the *other* composite, `ez_aw_homotopy` (proved for simplicial sets), to
topological spaces: the Eilenberg–Zilber shuffle map followed by the Alexander–Whitney map is
chain homotopic to the identity on `C_*(X) ⊗_ℤ C_*(Y)`:

`ez_aw_homotopyT X Y : Nonempty (Homotopy (ezMapT X Y ≫ awMapT X Y) 𝟙)`.

The transport is the same as in `aw_ez_homotopyT`: the monoidal structure of `TopCat.toSSet`
identifies `Sing (X ⊗ Y)` with `Sing X ⊗ Sing Y`, and the two induced chain maps are mutually
inverse, so they can be cancelled from the composite `ezMapT ≫ awMapT`, leaving `ezMap ≫ awMap`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The transport chain maps of `singProdIso` cancel in the order needed for `ezMapT ≫ awMapT`:
`chainComplexMap inv ≫ chainComplexMap hom = 𝟙`. -/
theorem chainComplexMap_singProdIso_inv_comp (X Y : TopCat) :
    CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (singProdIso X Y).inv zz)
        (SSet.chainComplexMap (singProdIso X Y).hom zz)
      = CategoryTheory.CategoryStruct.id
          (sChain (sProd (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))) := by
  rw [← Functor.map_comp, Iso.inv_hom_id]
  exact CategoryTheory.Functor.map_id _ _

/-- After cancelling the transport, `ezMapT ≫ awMapT` is the simplicial composite `ezMap ≫ awMap`
on `Sing X` and `Sing Y`. -/
theorem ezMapT_comp_awMapT (X Y : TopCat) :
    CategoryTheory.CategoryStruct.comp (ezMapT X Y) (awMapT X Y)
      = CategoryTheory.CategoryStruct.comp (ezMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))
          (awMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)) := by
  have h1 : CategoryTheory.CategoryStruct.comp
        (SSet.chainComplexMap (singProdIso X Y).inv zz)
        (SSet.chainComplexMap (singProdIso X Y).hom zz)
      = 𝟙 (sChain (sProd (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))) :=
    chainComplexMap_singProdIso_inv_comp X Y
  have h2 : CategoryTheory.CategoryStruct.comp
        (SSet.chainComplexMap (singProdIso X Y).inv zz)
        (CategoryTheory.CategoryStruct.comp
          (SSet.chainComplexMap (singProdIso X Y).hom zz)
          (awMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)))
      = awMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) := by
    rw [← Category.assoc, h1, Category.id_comp]
  simp only [ezMapT, awMapT, Category.assoc, h2]

/-- **The Eilenberg–Zilber homotopy `EZ ∘ AW ≃ 𝟙` for topological spaces**, transported from the
simplicial statement `Work.Kunneth.ez_aw_homotopy`. -/
theorem ez_aw_homotopyT (X Y : TopCat) :
    Nonempty (Homotopy
      (CategoryTheory.CategoryStruct.comp (Work.Kunneth.ezMapT X Y) (Work.Kunneth.awMapT X Y))
      (CategoryTheory.CategoryStruct.id (Work.Kunneth.tChain (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)))) := by
  obtain ⟨H⟩ := ez_aw_homotopy (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
  exact ⟨(Homotopy.ofEq (ezMapT_comp_awMapT X Y)).trans H⟩

end

end Work.Kunneth

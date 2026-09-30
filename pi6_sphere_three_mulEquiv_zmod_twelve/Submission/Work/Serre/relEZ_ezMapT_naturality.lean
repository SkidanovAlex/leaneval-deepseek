import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Kunneth.TopCat

/-!
# Naturality of the Eilenberg–Zilber map `ezMapT` for topological spaces

`Work.Kunneth.ezMapT X Y : C_*(X) ⊗_ℤ C_*(Y) ⟶ C_*(X × Y)` is the shuffle chain map of the
Eilenberg–Zilber theorem, obtained from the simplicial shuffle map `Work.Kunneth.ezMap` by
transporting along `Work.Kunneth.singProdIso X Y : Sing (X × Y) ≅ Sing X ⊗ Sing Y`.

Here we prove that it is natural: the square

`C_*(X) ⊗_ℤ C_*(Y) --ezMapT X Y--> C_*(X × Y)`
`          |                                |`
`ind (C_* f) (C_* g)                C_*(f × g)`
`          v                                v`
`C_*(X') ⊗_ℤ C_*(Y') -ezMapT X' Y'-> C_*(X' × Y')`

commutes.  The simplicial content is `Work.Kunneth.ezaw_ezMap_naturality`; the only genuinely new
ingredient is the naturality of the tensorator of the monoidal functor `TopCat.toSSet`, i.e.
`CategoryTheory.Functor.LaxMonoidal.μ_natural`, which is exactly the naturality of the transport
`singProdIso` used to define the topological Eilenberg–Zilber map.
-/

set_option autoImplicit false

open CategoryTheory

namespace Work.Serre

noncomputable section

/-- Naturality of `Work.Kunneth.singProdIso` (`= (μIso TopCat.toSSet - -).symm`), in the form
needed to compare the two transports `Sing (X × Y) ≅ Sing X ⊗ Sing Y` along a product of maps. -/
lemma singProdIso_inv_naturality (X Y X' Y' : TopCat) (f : X ⟶ X') (g : Y ⟶ Y') :
    CategoryTheory.CategoryStruct.comp (Work.Kunneth.singProdIso X Y).inv
        (TopCat.toSSet.map (CategoryTheory.MonoidalCategoryStruct.tensorHom f g))
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.MonoidalCategoryStruct.tensorHom (TopCat.toSSet.map f)
            (TopCat.toSSet.map g))
          (Work.Kunneth.singProdIso X' Y').inv := by
  simpa [Work.Kunneth.singProdIso] using
    (CategoryTheory.Functor.LaxMonoidal.μ_natural TopCat.toSSet f g).symm

/-- The previous identity transported to singular chain complexes: the two ways of transporting
the tensor product of `C_*(X)` and `C_*(Y)` to `C_*(X' × Y')` agree. -/
lemma singProdIso_chainMap_comm (X Y X' Y' : TopCat) (f : X ⟶ X') (g : Y ⟶ Y') :
    CategoryTheory.CategoryStruct.comp
        (SSet.chainComplexMap
          (CategoryTheory.MonoidalCategoryStruct.tensorHom (TopCat.toSSet.map f)
            (TopCat.toSSet.map g))
          Work.Kunneth.zz)
        (SSet.chainComplexMap (Work.Kunneth.singProdIso X' Y').inv Work.Kunneth.zz)
      = CategoryTheory.CategoryStruct.comp
        (SSet.chainComplexMap (Work.Kunneth.singProdIso X Y).inv Work.Kunneth.zz)
        (SSet.chainComplexMap
          (TopCat.toSSet.map (CategoryTheory.MonoidalCategoryStruct.tensorHom f g))
          Work.Kunneth.zz) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    singProdIso_inv_naturality]

theorem relEZ_ezMapT_naturality (X Y X' Y' : TopCat) (f : X ⟶ X') (g : Y ⟶ Y') :
    CategoryTheory.CategoryStruct.comp
      (Work.Kunneth.tpMap (Work.Kunneth.sChain (TopCat.toSSet.obj X))
        (Work.Kunneth.sChain (TopCat.toSSet.obj X'))
        (Work.Kunneth.sChain (TopCat.toSSet.obj Y)) (Work.Kunneth.sChain (TopCat.toSSet.obj Y'))
        (SSet.chainComplexMap (TopCat.toSSet.map f) Work.Kunneth.zz)
        (SSet.chainComplexMap (TopCat.toSSet.map g) Work.Kunneth.zz))
      (Work.Kunneth.ezMapT X' Y')
    = CategoryTheory.CategoryStruct.comp (Work.Kunneth.ezMapT X Y)
      (SSet.chainComplexMap
        (TopCat.toSSet.map (CategoryTheory.MonoidalCategoryStruct.tensorHom f g))
        Work.Kunneth.zz) := by
  have hnat := Work.Kunneth.ezaw_ezMap_naturality (TopCat.toSSet.map f) (TopCat.toSSet.map g)
  have hmid := singProdIso_chainMap_comm X Y X' Y' f g
  change CategoryTheory.CategoryStruct.comp
        (Work.Kunneth.ind (TopCat.toSSet.map f) (TopCat.toSSet.map g))
        (CategoryTheory.CategoryStruct.comp
          (Work.Kunneth.ezMap (TopCat.toSSet.obj X') (TopCat.toSSet.obj Y'))
          (SSet.chainComplexMap (Work.Kunneth.singProdIso X' Y').inv Work.Kunneth.zz))
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp
            (Work.Kunneth.ezMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))
            (SSet.chainComplexMap (Work.Kunneth.singProdIso X Y).inv Work.Kunneth.zz))
          (SSet.chainComplexMap
            (TopCat.toSSet.map (CategoryTheory.MonoidalCategoryStruct.tensorHom f g))
            Work.Kunneth.zz)
  rw [← CategoryTheory.Category.assoc, hnat, CategoryTheory.Category.assoc, hmid,
    CategoryTheory.Category.assoc]

end

end Work.Serre

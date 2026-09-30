import Mathlib
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

namespace Work.Homology

/-- A homeomorphism `e : X ≃ₜ Y` regarded as a morphism `X ⟶ Y` of `TopCat`. -/
def homeomorphTopCatHom {X Y : TopCat} (e : X ≃ₜ Y) : X ⟶ Y :=
  TopCat.ofHom ⟨e.toFun, e.continuous_toFun⟩

/-- The inverse of `homeomorphTopCatHom e`, as a morphism `Y ⟶ X` of `TopCat`. -/
def homeomorphTopCatInv {X Y : TopCat} (e : X ≃ₜ Y) : Y ⟶ X :=
  TopCat.ofHom ⟨e.invFun, e.continuous_invFun⟩

@[simp]
theorem homeomorphTopCatHom_apply {X Y : TopCat} (e : X ≃ₜ Y) (x : X) :
    (homeomorphTopCatHom e) x = e x := rfl

@[simp]
theorem homeomorphTopCatInv_apply {X Y : TopCat} (e : X ≃ₜ Y) (y : Y) :
    (homeomorphTopCatInv e) y = e.symm y := rfl

theorem homeomorphTopCatHom_comp_inv {X Y : TopCat} (e : X ≃ₜ Y) :
    homeomorphTopCatHom e ≫ homeomorphTopCatInv e = 𝟙 X := by
  apply TopCat.hom_ext
  ext x
  simp [homeomorphTopCatHom, homeomorphTopCatInv, TopCat.ofHom]

theorem homeomorphTopCatInv_comp_hom {X Y : TopCat} (e : X ≃ₜ Y) :
    homeomorphTopCatInv e ≫ homeomorphTopCatHom e = 𝟙 Y := by
  apply TopCat.hom_ext
  ext y
  simp [homeomorphTopCatHom, homeomorphTopCatInv, TopCat.ofHom]

/-- A homeomorphism induces an isomorphism on singular homology with coefficients
in any `R : ModuleCat ℤ`, in every degree. -/
theorem SingHomologyHomeomorph (R : ModuleCat ℤ) (k : ℕ) {X Y : TopCat} (e : X ≃ₜ Y) :
    Nonempty (singHomology R k X ≅ singHomology R k Y) :=
  ⟨{ hom := singHomologyMap R k (homeomorphTopCatHom e)
     inv := singHomologyMap R k (homeomorphTopCatInv e)
     hom_inv_id := by
       rw [← singHomologyMap_comp, homeomorphTopCatHom_comp_inv, singHomologyMap_id]
     inv_hom_id := by
       rw [← singHomologyMap_comp, homeomorphTopCatInv_comp_hom, singHomologyMap_id] }⟩

end Work.Homology

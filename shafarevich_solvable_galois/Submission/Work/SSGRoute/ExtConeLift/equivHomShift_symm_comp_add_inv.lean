import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtConeLift

open CategoryTheory Limits CochainComplex HomComplex

universe u v

/-- The inverse of an `XIsoOfEq` induced by a *reflexive* equality of degrees is the identity.
This is the normalization used in the shift bookkeeping below: all the `XIsoOfEq` morphisms
occurring there relate objects that are definitionally equal, so their inverses are `𝟙`. -/
lemma XIsoOfEq_self_inv {C : Type u} [Category.{v} C] [Preadditive C]
    {K : CochainComplex C ℤ} {i : ℤ} (h : i = i) :
    (K.XIsoOfEq h).inv = 𝟙 (K.X i) := by
  rw [Subsingleton.elim h rfl, HomologicalComplex.XIsoOfEq_rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Shift bookkeeping: for a cocycle `z : K ⟶ L⟦1⟧` of degree `n`, the morphism
`equivHomShift.symm z` (a chain map `K ⟶ (L⟦1⟧)⟦n⟧`) followed by the shift isomorphism
`(L⟦1⟧)⟦n⟧ ≅ L⟦n+1⟧` is the chain map associated with the unshifted cocycle `z.rightUnshift (n+1)`.

NB: `CategoryTheory.shiftFunctorAdd'` is written qualified because both `CategoryTheory` and
`CochainComplex` expose a `shiftFunctorAdd'`. -/
theorem equivHomShift_symm_comp_add_inv {C : Type u} [Category.{v} C] [Preadditive C]
    {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K (L⟦(1 : ℤ)⟧) n) :
    Cocycle.equivHomShift.symm z ≫
        (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) (1 : ℤ) n (n + 1)
          (by omega)).inv.app L =
      Cocycle.equivHomShift.symm (z.rightUnshift (n + 1) (by omega)) := by
  rw [Cocycle.equivHomShift_symm_apply, Cocycle.equivHomShift_symm_apply]
  ext p
  simp only [HomologicalComplex.comp_f, Cocycle.homOf_f, Cocycle.rightShift_coe,
    Cochain.rightShift_v, Cochain.rightUnshift_v, Cocycle.rightUnshift_coe,
    CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorObjXIso,
    XIsoOfEq_self_inv, Category.comp_id]

end Work.SSGRoute.ExtConeLift

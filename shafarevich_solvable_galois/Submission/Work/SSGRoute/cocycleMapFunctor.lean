import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The image of a cocycle of cochain complexes under an additive functor

Mathlib's `CochainComplex.HomComplex.Cocycle K L n` is an additive group (a subtype of
`Cochain K L n`), and `Cocycle.equivHomShift` identifies it with `K ⟶ L⟦n⟧`.  What is missing is
its behaviour under an additive functor `F : C ⥤ D`: the image cocycle (componentwise `F.map`) and
the compatibility with `equivHomShift`, which is the form in which the functoriality of `F` is
needed for the computation of `Abelian.Ext.mapExactFunctor` on `extMk`-classes.
-/

open CategoryTheory Limits

universe u v u' v'

namespace Work.SSGRoute

open CochainComplex.HomComplex

/-- The cochain of degree `n` obtained from a cochain `z : Cochain K L n` by applying an additive
functor componentwise. -/
noncomputable def cochainMapFunctor {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n : ℤ} (z : Cochain K L n) :
    Cochain ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n :=
  Cochain.mk (fun p q _ => F.map (z.v p q ‹p + n = q›))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma cochainMapFunctor_v {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n : ℤ} (z : Cochain K L n)
    (p q : ℤ) (hpq : p + n = q) :
    (cochainMapFunctor F z).v p q hpq = F.map (z.v p q hpq) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `F` commutes with the differential `δ` on cochains. -/
lemma cochainMapFunctor_δ {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n m : ℤ} (z : Cochain K L n) :
    cochainMapFunctor F (δ n m z) = δ n m (cochainMapFunctor F z) := by
  ext p q hpq
  simp only [Cochain.mk_v, cochainMapFunctor, δ, Functor.map_add, Functor.map_comp,
    Functor.map_zsmul, Units.smul_def, Functor.mapHomologicalComplex_obj_d]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma cochainMapFunctor_zero {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n : ℤ} :
    cochainMapFunctor F (0 : Cochain K L n) = 0 := by
  ext p q hpq
  simp only [cochainMapFunctor, Cochain.mk_v, Cochain.zero_v, Functor.map_zero]

/-- The image of a cocycle of cochain complexes under an additive functor. -/
noncomputable def cocycleMapFunctor {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    Cocycle ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n :=
  Cocycle.mk (cochainMapFunctor F (z : Cochain K L n)) (n + 1) rfl (by
    rw [← cochainMapFunctor_δ, Cocycle.δ_eq_zero]
    exact cochainMapFunctor_zero F)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma cocycleMapFunctor_coe {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    ((cocycleMapFunctor F z : Cocycle _ _ n) : Cochain _ _ n)
      = cochainMapFunctor F (z : Cochain K L n) := rfl

end Work.SSGRoute

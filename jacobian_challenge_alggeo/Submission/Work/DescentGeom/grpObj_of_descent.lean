import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open CategoryTheory

open scoped CategoryTheory MonObj MonoidalCategory

universe u v v' u'

namespace Work.DescentGeom

/-!
# Descent of a group-object structure along a faithful product-preserving functor

The main technical lemma of this file, `grpObj_of_faithful_productPreserving`, is a purely
categorical statement: if `F : C ⥤ D` is a faithful functor between Cartesian monoidal categories
which preserves finite products, and if `F.obj X` carries a group-object structure whose
multiplication/unit/inverse are the `F`-images of morphisms `mul`, `one`, `inv` on `X` (up to the
canonical comparison isomorphisms `prodComparisonIso` and `preservesTerminalIso`), then the group
structure descends to `X`.

The point is that `F` is monoidal for the structure maps `δ F`, `μ F`, `η F`, `ε F` determined by
the product comparisons, so that `Functor.Monoidal.map_tensor`, `map_associator`,
`map_leftUnitor` and `map_rightUnitor` express the `F`-image of every structure morphism of `X` in
terms of the corresponding structure morphism of `F.obj X`; the group axioms for `X` are then the
`δ`/`μ`-conjugates of the group axioms for `F.obj X`, and since `F` is faithful it suffices to
check them after applying `F`.

The intended application (the theorem `grpObj_of_descent` below) is `F = bcFun k k'`, the base
change functor `Sch k ⥤ Sch k'`, which is faithful (`map_injective`) and preserves finite products
(it is a right adjoint).
-/

/-- **Group structures descend along a faithful product-preserving functor.**

Let `F : C ⥤ D` be a faithful functor between Cartesian monoidal categories which preserves finite
products.  If the `F`-image of `J` carries a group-object structure with multiplication, unit and
inverse the `F`-images of `mul`, `one` and `inv` under the product/terminal comparison
isomorphisms, then `J` itself carries a group-object structure with those structure morphisms. -/
theorem grpObj_of_faithful_productPreserving {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [Limits.PreservesFiniteProducts F] [F.Faithful]
    (X : C) [GrpObj (F.obj X)]
    (mul : X ⊗ X ⟶ X) (one : 𝟙_ C ⟶ X) (inv : X ⟶ X)
    (hμ : F.map mul = (CartesianMonoidalCategory.prodComparisonIso F X X).hom ≫ μ[F.obj X])
    (hη : F.map one = (CartesianMonoidalCategory.preservesTerminalIso F).hom ≫ η[F.obj X])
    (hι : F.map inv = ι[F.obj X]) :
    ∃ m : GrpObj X, m.mul = mul ∧ m.one = one ∧ m.inv = inv := by
  letI : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts F
  -- Rewrite the two comparison isomorphisms into the `δ`/`η` of the monoidal structure of `F`.
  have hμ' : F.map mul = Functor.OplaxMonoidal.δ F X X ≫ μ[F.obj X] := by
    rw [hμ, CartesianMonoidalCategory.prodComparisonIso_hom,
      ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
  have hη' : F.map one = Functor.OplaxMonoidal.η F ≫ η[F.obj X] := by
    rw [hη, CartesianMonoidalCategory.preservesTerminalIso_hom,
      ← Functor.OplaxMonoidal.η_of_cartesianMonoidalCategory]
  -- `η F` is the comparison `F.obj (𝟙_ C) ⟶ 𝟙_ D`, so it can be absorbed into `toUnit`:
  have h0 : F.map (SemiCartesianMonoidalCategory.toUnit X) ≫ Functor.OplaxMonoidal.η F =
      SemiCartesianMonoidalCategory.toUnit (F.obj X) :=
    CartesianMonoidalCategory.map_toUnit_comp_terminalComparison F X
  have hR : F.map (SemiCartesianMonoidalCategory.toUnit X) ≫
      (Functor.OplaxMonoidal.η F ≫ η[F.obj X]) =
      SemiCartesianMonoidalCategory.toUnit (F.obj X) ≫ η[F.obj X] := by
    rw [← Category.assoc, h0]
  have h_one_mul : one ▷ X ≫ mul = (λ_ X).hom := by
    apply F.map_injective
    rw [Functor.map_comp, Functor.Monoidal.map_whiskerRight, hη', hμ',
      Functor.Monoidal.map_leftUnitor]
    simp [MonObj.one_mul]
  have h_mul_one : X ◁ one ≫ mul = (ρ_ X).hom := by
    apply F.map_injective
    rw [Functor.map_comp, Functor.Monoidal.map_whiskerLeft, hη', hμ',
      Functor.Monoidal.map_rightUnitor]
    simp [MonoidalCategory.whiskerLeft_comp, MonObj.mul_one]
  have h_mul_assoc : mul ▷ X ≫ mul = (α_ X X X).hom ≫ X ◁ mul ≫ mul := by
    apply F.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
      Functor.Monoidal.map_whiskerRight, hμ',
      Functor.Monoidal.map_associator, Functor.Monoidal.map_whiskerLeft, hμ']
    simp [MonObj.mul_assoc]
  have h_left_inv : CartesianMonoidalCategory.lift inv (𝟙 X) ≫ mul =
      SemiCartesianMonoidalCategory.toUnit X ≫ one := by
    apply F.map_injective
    rw [Functor.map_comp, ← Functor.Monoidal.lift_μ F inv (𝟙 X), hι, hμ',
      Functor.map_comp, hη', hR]
    simp
  have h_right_inv : CartesianMonoidalCategory.lift (𝟙 X) inv ≫ mul =
      SemiCartesianMonoidalCategory.toUnit X ≫ one := by
    apply F.map_injective
    rw [Functor.map_comp, ← Functor.Monoidal.lift_μ F (𝟙 X) inv, hι, hμ',
      Functor.map_comp, hη', hR]
    simp
  exact ⟨GrpObj.mk (toMonObj := MonObj.mk one mul h_one_mul h_mul_one h_mul_assoc) inv
    h_left_inv h_right_inv, rfl, rfl, rfl⟩

/-- **Descent of the group-object structure along the base change `Sch k ⥤ Sch k'`.**

The base change functor `bcFun k k'` is faithful (`map_injective`) and preserves finite products
(it is `Over.pullback (Spec.map (algebraMap k k'))`, a right adjoint), so a group-object structure
on `bc k' J` whose structure morphisms are the base changes of `mul`, `one`, `inv` descends to
`J`. -/
theorem grpObj_of_descent {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (J : Work.DescentGeom.Sch k) [GrpObj (Work.DescentGeom.bc k' J)]
    (mul : J ⊗ J ⟶ J) (one : 𝟙_ (Work.DescentGeom.Sch k) ⟶ J) (inv : J ⟶ J)
    (hμ : (Work.DescentGeom.bcFun k k').map mul =
      (CartesianMonoidalCategory.prodComparisonIso (Work.DescentGeom.bcFun k k') J J).hom ≫
        μ[Work.DescentGeom.bc k' J])
    (hη : (Work.DescentGeom.bcFun k k').map one =
      (CartesianMonoidalCategory.preservesTerminalIso (Work.DescentGeom.bcFun k k')).hom ≫
        η[Work.DescentGeom.bc k' J])
    (hι : (Work.DescentGeom.bcFun k k').map inv = ι[Work.DescentGeom.bc k' J]) :
    ∃ m : GrpObj J, m.mul = mul ∧ m.one = one ∧ m.inv = inv := by
  haveI : Functor.Faithful (Work.DescentGeom.bcFun k k') :=
    ⟨fun {X Y} => Work.DescentGeom.map_injective X Y⟩
  exact grpObj_of_faithful_productPreserving (Work.DescentGeom.bcFun k k') J mul one inv
    hμ hη hι

end Work.DescentGeom

/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area GenusZero
-/
import Submission.Work.GCBasics.hom_ext_of_resPt
import Submission.Work.KeyLemma.Final
import Submission.Work.AbVar.SmoothIntegral
import Submission.Work.DescentGeom.Basic
import Submission.Work.SpecLin.Points.ptDiv_deg
import Submission.Work.RiemannRoch.ExportCB

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GenusZero: the `g = 0` Jacobian package

This is the vocabulary file of area `GenusZero`, the chapter of the Jacobian drive which
handles the genus-zero case of the challenge, where the Jacobian is the trivial group scheme
`J = 𝟙_`.  Its mathematical content is that a *pointed* map from a genus-zero curve to an
abelian variety is constant; the genus-zero Jacobian package
`Work.Packaging.JacPkg C P0` is assembled from it in `Trivial.lean`.

## Conventions

* `Work.GenusZero.Sch k` is the category of `k`-schemes, `Over (Spec k)`; it is definitionally
  the `Work.GCBasics.Sch k` of the drive and the `Over (Spec (.of k))` of the challenge.
* `Work.GenusZero.bcFun F : Sch k ⥤ Sch F` is base change along a field extension `F/k`; it is
  the functor `Work.DescentGeom.bcFun k F` and hence the same as `Curve.baseChange`.
* `Work.GenusZero.toUnit X` is the unique morphism `X ⟶ 𝟙_ (Sch k)`
  (`toUnit_unique`).
* `Work.GenusZero.ptBaseChange F A x` base changes an `F`-point of a `k`-scheme `A`
  (`x : specOf k F ⟶ A`) to an `F`-point of the base change `A_F`.  This is the inverse of
  "compose with the projection `A_F ⟶ A`"; it is what allows the residue-field argument of
  `Rigidity.lean` to compare a morphism `specOf k F ⟶ A` over a *residue* field with points
  over the base field.

## Main results

* `Work.GenusZero.ptBaseChange_left_fst`, `…_injective`, `…_comp` — the API of base change of
  points: computation of the underlying morphism of schemes, injectivity, and naturality;
* `Work.GenusZero.bcFun_map_left_fst`, `…_snd` — the pullback functor on morphisms;
* `Work.GenusZero.genus_baseChange` — the genus is invariant under base change.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace Work.GenusZero

/-- The category of `k`-schemes: `Over (Spec k)`.  This is definitionally the `Sch k` of every
other area of the drive, and the `Over (Spec (.of k))` of the challenge statement. -/
abbrev Sch (k : Type u) [Field k] : Type (u + 1) := Over (Spec (CommRingCat.of k))

/-- `Spec R` as a `k`-scheme, for `R` a `k`-algebra. -/
noncomputable abbrev specOf (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R] :
    Sch k :=
  Work.GCBasics.specOf k R

variable {k : Type u} [Field k]

/-- The unique morphism from a `k`-scheme to the terminal object. -/
noncomputable abbrev toUnit (X : Sch k) : X ⟶ 𝟙_ (Sch k) :=
  SemiCartesianMonoidalCategory.toUnit X

/-- Two morphisms into the terminal object of `Sch k` are equal. -/
theorem toUnit_unique {X : Sch k} (f g : X ⟶ 𝟙_ (Sch k)) : f = g :=
  SemiCartesianMonoidalCategory.toUnit_unique f g

/-- The terminal object is a group object, and its unit section is its identity (both are
endomorphisms of the terminal object). -/
@[simp]
theorem toUnit_tensorUnit : toUnit (𝟙_ (Sch k)) = 𝟙 (𝟙_ (Sch k)) :=
  toUnit_unique _ _

/-- Base change of `k`-schemes along a field extension `F/k`.  It is `Work.DescentGeom.bcFun`,
hence the functor underlying `Curve.baseChange`. -/
noncomputable abbrev bcFun (F : Type u) [Field F] [Algebra k F] : Sch k ⥤ Sch F :=
  Work.DescentGeom.bcFun k F

/-- `Work.GenusZero.specOf` is `Work.GCBasics.specOf`, i.e. `Spec` of the structure
morphism. -/
theorem specOf_hom (F : Type u) [Field F] [Algebra k F] :
    (Work.GCBasics.specOf k F).hom = Work.Descent.specMap k F := rfl

/-- The genus is invariant under base change of the base field. -/
theorem genus_baseChange (C : CurveBasics.Curve k) (F : Type u) [Field F] [Algebra k F] :
    RiemannRoch.Curve.genus (C.baseChange F) = RiemannRoch.Curve.genus C :=
  RiemannRoch.Curve.genus_eq (CurveBasics.Curve.bcSquare C F)

/-! ## Base change of points

For a `k`-scheme `A` and a field extension `F/k` the `F`-points of `A` (morphisms
`specOf k F ⟶ A`, equivalently sections of `A.hom` over `Spec k`) correspond to the `F`-points
of the base change `A_F`: the functor `Over.pullback (specMap k F)` has the left adjoint
`Over.map (specMap k F)`, and on the unit objects this adjunction is the desired equivalence.
Here it is written out explicitly as a `pullback.lift`, so that every computation happens in
the ambient category of schemes. -/

/-- The commutativity of the square defining `ptBaseChange`. -/
theorem ptBaseChange_witness (F : Type u) [Field F] [Algebra k F] (A : Sch k)
    (x : Work.GCBasics.specOf k F ⟶ A) :
    Over.Hom.left x ≫ Over.hom A = 𝟙 (Spec (CommRingCat.of F)) ≫
      Work.Descent.specMap k F :=
  (Over.w x).trans (Category.id_comp _).symm

/-- The base change of an `F`-point of a `k`-scheme `A` to an `F`-point of `A_F`.

If `x : specOf k F ⟶ A` is a section of `A.hom` over `Spec k` and `A_F = A ×_k Spec F` is the
base change, then `ptBaseChange F A x` is the section of `A_F ⟶ Spec F` induced by `x` and the
identity of `Spec F`. -/
noncomputable def ptBaseChange (F : Type u) [Field F] [Algebra k F]
    (A : Sch k) (x : Work.GCBasics.specOf k F ⟶ A) :
    𝟙_ (Sch F) ⟶ (bcFun F).obj A :=
  Over.homMk (pullback.lift x.left (𝟙 (Spec (CommRingCat.of F))) (ptBaseChange_witness F A x))
    (by
      change pullback.lift x.left (𝟙 (Spec (CommRingCat.of F))) (ptBaseChange_witness F A x) ≫
        pullback.snd A.hom (Work.Descent.specMap k F) = 𝟙 (Spec (CommRingCat.of F))
      exact pullback.lift_snd _ _ _)

/-- The underlying morphism of schemes of `ptBaseChange F A x` is the `pullback.lift` of
`x.left` against the identity of `Spec F`. -/
theorem ptBaseChange_left (F : Type u) [Field F] [Algebra k F]
    (A : Sch k) (x : Work.GCBasics.specOf k F ⟶ A) :
    (ptBaseChange F A x).left =
      pullback.lift x.left (𝟙 (Spec (CommRingCat.of F))) (ptBaseChange_witness F A x) :=
  rfl

/-- `ptBaseChange F A x` projects to `x` along the projection `A_F ⟶ A`. -/
theorem ptBaseChange_left_fst (F : Type u) [Field F] [Algebra k F]
    (A : Sch k) (x : Work.GCBasics.specOf k F ⟶ A) :
    (ptBaseChange F A x).left ≫ pullback.fst A.hom (Work.Descent.specMap k F) = x.left := by
  rw [ptBaseChange_left, pullback.lift_fst]

/-- `ptBaseChange F A` is injective: an `F`-point of `A` over `Spec k` is determined by its
base change to `A_F`. -/
theorem ptBaseChange_injective (F : Type u) [Field F] [Algebra k F] (A : Sch k) :
    Function.Injective (ptBaseChange (k := k) F A) := by
  intro x y h
  have hleft : (ptBaseChange (k := k) F A x).left = (ptBaseChange (k := k) F A y).left :=
    congrArg Over.Hom.left h
  apply Over.OverMorphism.ext
  rw [← ptBaseChange_left_fst (k := k) F A x, ← ptBaseChange_left_fst (k := k) F A y, hleft]

/-- The pullback functor composed with the projection to the first factor: the underlying
morphism of schemes of `(bcFun F).map g` is compatible with the projections `A_F ⟶ A`. -/
theorem bcFun_map_left_fst {A B : Sch k} (F : Type u) [Field F] [Algebra k F] (g : A ⟶ B) :
    ((bcFun F).map g).left ≫ pullback.fst B.hom (Work.Descent.specMap k F) =
      pullback.fst A.hom (Work.Descent.specMap k F) ≫ g.left := by
  simp only [bcFun, Work.DescentGeom.bcFun, Work.Descent.baseChangeFunctor,
    Over.pullback_map_left, pullback.lift_fst]

/-- The pullback functor on morphisms, on the second factor. -/
theorem bcFun_map_left_snd {A B : Sch k} (F : Type u) [Field F] [Algebra k F] (g : A ⟶ B) :
    ((bcFun F).map g).left ≫ pullback.snd B.hom (Work.Descent.specMap k F) =
      pullback.snd A.hom (Work.Descent.specMap k F) := by
  simp only [bcFun, Work.DescentGeom.bcFun, Work.Descent.baseChangeFunctor,
    Over.pullback_map_left, pullback.lift_snd]

/-- `ptBaseChange` is natural: base changing a composite is the composite of the base
changes. -/
theorem ptBaseChange_comp (F : Type u) [Field F] [Algebra k F]
    {A B : Sch k} (x : Work.GCBasics.specOf k F ⟶ A) (g : A ⟶ B) :
    ptBaseChange F B (x ≫ g) = ptBaseChange F A x ≫ (bcFun F).map g := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  apply pullback.hom_ext
  · rw [Category.assoc, ptBaseChange_left_fst, bcFun_map_left_fst, ← Category.assoc,
      ptBaseChange_left_fst, Over.comp_left]
  · rw [ptBaseChange_left, ptBaseChange_left, Category.assoc, bcFun_map_left_snd,
      pullback.lift_snd, pullback.lift_snd]

/-! ## Base change of abelian varieties

The base change `A_F` of an abelian variety is an abelian variety, and (therefore) a commutative
group scheme.  The instances for `Smooth`, `IsProper` and `GeometricallyIrreducible` are those of
Mathlib, but the structure morphism of `(bcFun F).obj A` has to be unfolded to the `pullback.snd`
form first, which `change` does. -/

/-- The base change `A_F` of an abelian variety `A` is an abelian variety. -/
instance isAbelianVariety_bcFun (F : Type u) [Field F] [Algebra k F] (A : Sch k)
    [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] :
    Work.AbVar.IsAbelianVariety ((bcFun F).obj A) where
  smooth := by
    change Smooth (pullback.snd A.hom (Work.Descent.specMap k F))
    infer_instance
  isProper := by
    change IsProper (pullback.snd A.hom (Work.Descent.specMap k F))
    infer_instance
  geometricallyIrreducible := by
    change GeometricallyIrreducible (pullback.snd A.hom (Work.Descent.specMap k F))
    infer_instance

/-- The base change `A_F` of an abelian variety is a commutative group scheme. -/
instance isCommMonObj_bcFun (F : Type u) [Field F] [Algebra k F] (A : Sch k)
    [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A] :
    IsCommMonObj ((bcFun F).obj A) :=
  Work.AbVar.isCommMonObj_of_isAbelianVariety _

end Work.GenusZero

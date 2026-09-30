import Mathlib
import Submission.Work.BcDiv.Basic
import Submission.Work.SymQuot.DivBaseInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.BcDiv

universe u

/-- `divMap` of a composite of two base-change squares, in application form: the pullback
along `S.comp T` is the composite of the pullbacks along `T` and `S`. -/
private lemma divMap_comp_apply {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {F' : Type u} [Field F'] [Algebra F F'] [Algebra k F'] [IsScalarTower k F F']
    {C : Curve k} {C' : Curve F} {C'' : Curve F'}
    (S : Curve.BCSquare C C') (T : Curve.BCSquare C' C'') (D : C.Div) :
    (S.comp T).divMap D = T.divMap (S.divMap D) := by
  rw [Curve.BCSquare.divMap_comp]
  rfl

/-- **B4, compatibility with `DivBase.bc`.** Base changing divisors along the field extension
`e : F →ₐ[L] F'` commutes with the identification `Work.BcDiv.bcDiv` of the divisor groups of
`C_L` and `C` — the `K`-structure on `F'` being the restriction of scalars of `e`.

Here `Work.SpecLin.DivBase.bc` is SY's concrete pullback of divisors,
`Work.SymQuot.instDivBase` (`Submission/Work/SymQuot/DivBaseInst.lean`), i.e. the
ramification-weighted pullback along the tower square `bcSquareTower`; both sides therefore unfold
to `divMap` of a cartesian square between the models `(C_L)_F` and `C_{F'}` of the base change
of `C`.

Proof route: `Work.BcDiv.bcDiv_apply` and `Curve.BCSquare.divMap_comp` rewrite both sides as
`divMap` of a composite cartesian square; by `Work.BcDiv.BCSquare.ext_π` it suffices that the two
projections `C_{F'}.left ⟶ ((C_L)_F).left` agree, which is checked on the two pullback
projections of `(C_L)_F = C_L ×_L Spec F` (`IsPullback.hom_ext`), using
`BCSquareBaseChange.towerHom_fst`/`towerHom_snd`, `Work.BcDiv.BCSquare.cmp_π_comp`/`cmp_π_hom`
and `pullback.condition`. -/
theorem bcDiv_bc {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    {F' : Type u} [Field F'] [Algebra L F'] [Algebra K F'] [IsScalarTower K L F']
    (e : F →ₐ[L] F') (D : Work.GCBasics.Dv (C.baseChange L) F) :
    Work.BcDiv.bcDiv (Work.SpecLin.DivBase.bc e D)
      = Work.SpecLin.DivBase.bc (e.restrictScalars K) (Work.BcDiv.bcDiv D) := by
  -- unfold `bcDiv` on both sides
  rw [Work.BcDiv.bcDiv_apply, Work.BcDiv.bcDiv_apply]
  -- unfold the concrete `DivBase.bc` instance: the `F`-algebra structure on `F'` is `e`
  letI : Algebra F F' := e.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := Work.SymQuot.isScalarTower_of_algHom (e.restrictScalars K)
  show (Work.BcDiv.bcSq (C := C) (L := L) (F := F')).divMap
      ((Work.SymQuot.DivOf.bcSquareTower (C := C.baseChange L) F F').divMap D) =
    (Work.SymQuot.DivOf.bcSquareTower (C := C) F F').divMap
      ((Work.BcDiv.bcSq (C := C) (L := L) (F := F)).divMap D)
  -- the projections of the two composite squares agree
  have hπ : (Work.BcDiv.bcSq (C := C) (L := L) (F := F')).π ≫
      (Work.SymQuot.DivOf.bcSquareTower (C := C.baseChange L) F F').π
      = (Work.SymQuot.DivOf.bcSquareTower (C := C) F F').π ≫
        (Work.BcDiv.bcSq (C := C) (L := L) (F := F)).π := by
    show (Work.BcDiv.bcSq (C := C) (L := L) (F := F')).π ≫
        Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C.baseChange L) (F := F) (F' := F')
      = Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F') ≫
        (Work.BcDiv.bcSq (C := C) (L := L) (F := F)).π
    -- `(C_L)_F` is the fibre product `C_L ×_L Spec F`; it suffices to test on its two projections
    have ht : Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C.baseChange L)
          (F := F) (F' := F')
        ≫ (Work.BcDiv.sqLF (C := C) (L := L) (F := F)).π
        = (Work.BcDiv.sqLF (C := C) (L := L) (F := F')).π := by
      show Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C.baseChange L)
            (F := F) (F' := F')
          ≫ (Curve.baseChangeFst (C.baseChange L) F ≫ Curve.baseChangeFst C L)
        = (Curve.baseChangeFst (C.baseChange L) F' ≫ Curve.baseChangeFst C L)
      rw [← Category.assoc]
      congr 1
      exact Work.SymQuot.DivOf.BCSquareBaseChange.towerHom_fst (C := C.baseChange L)
        (F := F) (F' := F')
    have h1' : (Work.BcDiv.bcSq (C := C) (L := L) (F := F)).π ≫
        (Work.BcDiv.sqLF (C := C) (L := L) (F := F)).π
        = (Work.BcDiv.sqF (C := C) (F := F)).π :=
      Work.BcDiv.BCSquare.cmp_π_comp _ _
    have h2' : (Work.BcDiv.bcSq (C := C) (L := L) (F := F')).π ≫
        (Work.BcDiv.sqLF (C := C) (L := L) (F := F')).π
        = (Work.BcDiv.sqF (C := C) (F := F')).π :=
      Work.BcDiv.BCSquare.cmp_π_comp _ _
    have htC : Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F') ≫
        (Work.BcDiv.sqF (C := C) (F := F)).π = (Work.BcDiv.sqF (C := C) (F := F')).π :=
      Work.SymQuot.DivOf.BCSquareBaseChange.towerHom_fst (C := C) (F := F) (F' := F')
    have htS : Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C.baseChange L)
          (F := F) (F' := F')
        ≫ ((C.baseChange L).baseChange F).hom
        = ((C.baseChange L).baseChange F').hom ≫ Curve.specMap F F' :=
      Work.SymQuot.DivOf.BCSquareBaseChange.towerHom_snd (C := C.baseChange L) (F := F)
        (F' := F')
    have h2S : (Work.BcDiv.bcSq (C := C) (L := L) (F := F')).π ≫
        ((C.baseChange L).baseChange F').hom = (C.baseChange F').hom :=
      Work.BcDiv.BCSquare.cmp_π_hom _ _
    have h1S : (Work.BcDiv.bcSq (C := C) (L := L) (F := F)).π ≫
        ((C.baseChange L).baseChange F).hom = (C.baseChange F).hom :=
      Work.BcDiv.BCSquare.cmp_π_hom _ _
    have htCS : Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F')
        ≫ (C.baseChange F).hom = (C.baseChange F').hom ≫ Curve.specMap F F' :=
      Work.SymQuot.DivOf.BCSquareBaseChange.towerHom_snd (C := C) (F := F) (F' := F')
    refine IsPullback.hom_ext (Work.BcDiv.sqLF (C := C) (L := L) (F := F)).isPullback ?_ ?_
    · simp only [Category.assoc]
      rw [ht, h2', h1', htC]
    · simp only [Category.assoc]
      rw [htS]
      conv_lhs => rw [← Category.assoc]
      rw [h2S, h1S, htCS]
  -- both sides are `divMap` of the same composite square
  have hsq : (Work.SymQuot.DivOf.bcSquareTower (C := C.baseChange L) F F').comp
        (Work.BcDiv.bcSq (C := C) (L := L) (F := F')) =
      (Work.BcDiv.bcSq (C := C) (L := L) (F := F)).comp
        (Work.SymQuot.DivOf.bcSquareTower (C := C) F F') :=
    Work.BcDiv.BCSquare.ext_π hπ
  rw [← divMap_comp_apply (Work.SymQuot.DivOf.bcSquareTower (C := C.baseChange L) F F')
        (Work.BcDiv.bcSq (C := C) (L := L) (F := F')) D,
      ← divMap_comp_apply (Work.BcDiv.bcSq (C := C) (L := L) (F := F))
        (Work.SymQuot.DivOf.bcSquareTower (C := C) F F') D, hsq]

end Work.BcDiv

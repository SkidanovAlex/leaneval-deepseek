/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal
-/
import Mathlib
import Submission.Work.JacFinal.GalSym
import Submission.Work.SymQuot.BaseChange.exists_symBaseChangeIso
import Submission.Work.SymQuot.BaseChange.powMap_symBeta
import Submission.Work.Descent.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

universe u

namespace Work.JacFinal

noncomputable section

variable {k : Type u} [Field k]

/-- `Spec σ` is a morphism of `Spec k`-schemes: composing it with the structure morphism
`Spec k' ⟶ Spec k` gives the structure morphism again. -/
theorem specGal_comp_specMap {k' : Type u} [Field k'] [Algebra k k']
    (σ : Work.Descent.Gal k k') :
    Work.DescentGeom.specGal σ ≫ Work.CurveBasics.Curve.specMap k k' =
      Work.CurveBasics.Curve.specMap k k' := by
  rw [Work.DescentGeom.specGal, Work.CurveBasics.Curve.specMap, ← Spec.map_comp]
  congr 1
  ext c
  exact σ.commutes c

/-- For `u : X ⟶ Y` over `S` and `f : S' ⟶ S`, the underlying morphism of
`(Over.pullback f).map u` followed by the projection `Y ×_S S' ⟶ Y` is the projection
`X ×_S S' ⟶ X` followed by `u`. -/
theorem pullback_map_left_comp_fst {C' : Type*} [Category C'] {S S' : C'} (f : S' ⟶ S)
    [HasPullbacksAlong f] {X Y : Over S} (u : X ⟶ Y) :
    ((Over.pullback f).map u).left ≫ pullback.fst Y.hom f
      = pullback.fst X.hom f ≫ u.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-- **The diagonal Galois action on `C_{k'}^n` is killed by the base change projection.**

The underlying morphism of `d.galProd σ n`, composed with the projection
`(C_{k'})^n ⟶ C^n` (the base change along `Spec k' ⟶ Spec k`, read through the comparison
`symPiIso`), is that projection itself.  Equivalently: `galProd σ n` is a morphism over `Spec σ`,
and `Spec σ` fixes the structure morphism `Spec k' ⟶ Spec k`. -/
theorem galProd_comp_symPiIso {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    {P0 : 𝟙_ (Work.JacFinal.Sch k) ⟶ C.toOver} (d : Work.JacFinal.Inputs C P0) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] (σ : Work.Descent.Gal k d.k') :
    (d.galProd σ n).left ≫
      ((Work.SymQuot.BaseChange.symPiIso k d.k' C n).inv.left
        ≫ pullback.fst (Work.SymQuot.prod C.toOver n).hom (Work.CurveBasics.Curve.specMap k d.k'))
    = (Work.SymQuot.BaseChange.symPiIso k d.k' C n).inv.left
        ≫ pullback.fst (Work.SymQuot.prod C.toOver n).hom (Work.CurveBasics.Curve.specMap k d.k')
    := by
  let f := Work.CurveBasics.Curve.specMap k d.k'
  let T : Work.Descent.Sch k := Work.SymQuot.prod C.toOver n
  let Y : Work.Descent.Sch k := (Over.map f).obj (d.prodC n)
  let Cc : Work.Descent.Sch k := (Over.map f).obj ((Over.pullback f).obj C.toOver)
  -- ## 1. The projection `(C^n)_{k'} ⟶ C^n`, as a morphism `(Over.map f).obj Q ⟶ T`
  have hπTw : pullback.fst T.hom f ≫ T.hom
      = ((Over.map f).obj ((Over.pullback f).obj T)).hom := by
    rw [Over.map_obj_hom,
      show ((Over.pullback f).obj T).hom = pullback.snd T.hom f
        from Over.pullback_obj_hom f T]
    exact pullback.condition
  let πT : (Over.map f).obj ((Over.pullback f).obj T) ⟶ T :=
    Over.homMk (pullback.fst T.hom f) hπTw
  -- ## 2. The map `X` of the statement, as a morphism `Y ⟶ T` of `Sch k`
  let X_over : Y ⟶ T :=
    (Over.map f).map ((Work.SymQuot.BaseChange.symPiIso k d.k' C n).inv) ≫ πT
  -- ## 3. The diagonal action, as a morphism `Y ⟶ Y` of `Sch k`
  have hw : (d.galProd σ n).left ≫ (d.prodC n).hom
      = (d.prodC n).hom ≫ Work.DescentGeom.specGal σ := by
    have h := Over.w (d.galProd σ n)
    change (d.galProd σ n).left ≫ ((d.prodC n).hom ≫ Work.DescentGeom.specGal σ⁻¹)
      = (d.prodC n).hom at h
    have h2 := congrArg (fun t => t ≫ Work.DescentGeom.specGal σ) h
    simp only [Category.assoc] at h2
    rw [← Work.DescentGeom.specGal_mul (σ⁻¹) σ, inv_mul_cancel σ,
      Work.DescentGeom.specGal_one, Category.comp_id] at h2
    exact h2
  have hgw : (d.galProd σ n).left ≫ Y.hom = Y.hom := by
    change (d.galProd σ n).left ≫ ((Over.map f).obj (d.prodC n)).hom
      = ((Over.map f).obj (d.prodC n)).hom
    rw [Over.map_obj_hom, ← Category.assoc, hw, Category.assoc,
      show Work.DescentGeom.specGal σ ≫ f = f from specGal_comp_specMap σ]
  let galProd_over : Y ⟶ Y := Over.homMk ((d.galProd σ n).left) hgw
  -- ## 4. The `m`-th coordinate: the projection `Cc ⟶ C` and the Galois action on `C_{k'}`
  have hπCw : Work.Descent.baseChangeπ C.toOver ≫ C.toOver.hom = Cc.hom := by
    change Work.Descent.baseChangeπ C.toOver ≫ C.toOver.hom
      = (Work.Descent.baseChange C.toOver).hom ≫ f
    rw [Work.Descent.baseChangeπ_hom]
    rfl
  let πC : Cc ⟶ C.toOver := Over.homMk (Work.Descent.baseChangeπ C.toOver) hπCw
  have hgalw : Work.Descent.galAct C.toOver σ ≫ Cc.hom = Cc.hom := by
    have h := Work.Descent.galAct_hom C.toOver σ
    change Work.Descent.galAct C.toOver σ
        ≫ ((Work.Descent.baseChange C.toOver).hom ≫ f)
      = (Work.Descent.baseChange C.toOver).hom ≫ f
    rw [← Category.assoc, h, Category.assoc,
      show Work.DescentGeom.specGal σ ≫ f = f from specGal_comp_specMap σ]
  let galAct_over : Cc ⟶ Cc := Over.homMk (Work.Descent.galAct C.toOver σ) hgalw
  -- ## 5. The scheme-level coordinate computation
  have hXproj : ∀ m : Fin n,
      ((Work.SymQuot.BaseChange.symPiIso k d.k' C n).inv.left ≫ pullback.fst T.hom f)
          ≫ (Work.SymQuot.proj C.toOver n m).left
        = (d.projC n m).left ≫ pullback.fst C.toOver.hom f := by
    intro m
    have h1 : ((Over.pullback f).map (Work.SymQuot.proj C.toOver n m)).left
          ≫ pullback.fst C.toOver.hom f
        = pullback.fst T.hom f ≫ (Work.SymQuot.proj C.toOver n m).left :=
      pullback_map_left_comp_fst f (Work.SymQuot.proj C.toOver n m)
    have h2 : (Work.SymQuot.BaseChange.symPiIso k d.k' C n).inv.left
          ≫ ((Over.pullback f).map (Work.SymQuot.proj C.toOver n m)).left
        = (d.projC n m).left := by
      have h := congrArg Over.Hom.left
        (Work.SymQuot.BaseChange.symPiIso_inv_map_proj (K := k) (C := C) (L := d.k') n m)
      rw [Over.comp_left] at h
      exact h
    rw [Category.assoc, ← h1, ← Category.assoc, h2]
    try rfl
  -- ## 6. The three compatibility statements
  have key : ∀ m : Fin n,
      galProd_over ≫ (X_over ≫ Work.SymQuot.proj C.toOver n m)
        = X_over ≫ Work.SymQuot.proj C.toOver n m := by
    intro m
    let p_m : Y ⟶ Cc := (Over.map f).map (d.projC n m)
    have hA : X_over ≫ Work.SymQuot.proj C.toOver n m = p_m ≫ πC := by
      apply Over.OverMorphism.ext
      change ((Work.SymQuot.BaseChange.symPiIso k d.k' C n).inv.left ≫ pullback.fst T.hom f)
          ≫ (Work.SymQuot.proj C.toOver n m).left
        = (d.projC n m).left ≫ Work.Descent.baseChangeπ C.toOver
      exact hXproj m
    have hB : galProd_over ≫ p_m = p_m ≫ galAct_over := by
      apply Over.OverMorphism.ext
      change (d.galProd σ n).left ≫ (d.projC n m).left
        = (d.projC n m).left ≫ Work.Descent.galAct C.toOver σ
      have h := congrArg Over.Hom.left (d.galProd_proj σ n m)
      simp only [Over.comp_left, Work.JacFinal.Gal.tw, Over.map_map_left,
        Inputs.semilinC_left] at h
      exact h
    have hC : galAct_over ≫ πC = πC := by
      apply Over.OverMorphism.ext
      change Work.Descent.galAct C.toOver σ ≫ Work.Descent.baseChangeπ C.toOver
        = Work.Descent.baseChangeπ C.toOver
      exact Work.Descent.galAct_π C.toOver σ
    calc galProd_over ≫ (X_over ≫ Work.SymQuot.proj C.toOver n m)
        = galProd_over ≫ (p_m ≫ πC) := by rw [hA]
      _ = (galProd_over ≫ p_m) ≫ πC := (Category.assoc _ _ _).symm
      _ = (p_m ≫ galAct_over) ≫ πC := by rw [hB]
      _ = p_m ≫ (galAct_over ≫ πC) := Category.assoc _ _ _
      _ = p_m ≫ πC := by rw [hC]
      _ = X_over ≫ Work.SymQuot.proj C.toOver n m := hA.symm
  -- ## 7. Conclusion by the product universal property
  have hmain : galProd_over ≫ X_over = X_over :=
    Limits.Pi.hom_ext (galProd_over ≫ X_over) X_over key
  have hleft := congrArg Over.Hom.left hmain
  rw [Over.comp_left] at hleft
  exact hleft

end

end Work.JacFinal

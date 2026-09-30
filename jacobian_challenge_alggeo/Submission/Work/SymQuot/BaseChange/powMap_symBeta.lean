/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `powMap` and the base-change comparison `symβ` (area SY / BcDiv, B6)

For fields `K → L → F`, a curve `C` over `K` and `n` points `x_0, …, x_{n-1}` of the base
change `C_L` with values in `F`, the comparison `symβ : Symⁿ(C_L) ⟶ (Symⁿ C)_L` carries the
sum `x_0 + ⋯ + x_{n-1}` (a point of `Symⁿ(C_L)` over `F`, hence of `Symⁿ C` after projecting
along `βK = symβ ≫ pullback.fst`) to the sum of the projections to `C`:

`(Sym.powMap (C_L) n x ≫ symβ).left ≫ pullback.fst _ _ = (Sym.powMap C n (projOfBaseChange ∘ x)).left`

This is the coherence `powMap_βK` used by area `BcDiv` (see
`Submission/Work/NOTES_LEAD_jacobian_gaps2.md`, B6).
-/
import Mathlib
import Submission.Work.SymQuot.BaseChange.PowMapBeta
import Submission.Work.BcDiv.PbPt
import Submission.Work.BcDiv.Points

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option allowUnsafeReducibility true

universe u

namespace Work.SymQuot.BaseChange

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped MonoidalCategory

/-! The comparison `symPiIso : (Cⁿ)_L ≅ (C_L)ⁿ` is an isomorphism in `Over (Spec L)`, while
`Work.SymQuot.prod` is opaque: to compare the two definitions of the `n`-fold product in
`Over (Spec L)` we mark it reducible locally. -/
attribute [local reducible] Work.SymQuot.prod

section Helpers

variable {K : Type u} [Field K] {C : Curve K}
  [Work.SymQuot.CurveAffineCover C] {L : Type u} [Field L] [Algebra K L]
  {F : Type u} [Field F] [Algebra K F] [Algebra L F] [IsScalarTower K L F]

/-- The inverse of the base-change comparison `(Cⁿ)_L ≅ (C_L)ⁿ`, composed with the `m`-th
projection of `Cⁿ`, is the `m`-th projection of `(C_L)ⁿ`. -/
theorem pbPiIso_inv_map_proj (n : ℕ) (m : Fin n) :
    (pbPiIso (Curve.specMap K L) C.toOver n).inv ≫
        (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.proj C.toOver n m)
      = Work.SymQuot.proj ((Over.pullback (Curve.specMap K L)).obj C.toOver) n m := by
  rw [← pbPiIso_hom_proj (Curve.specMap K L) C.toOver n m, ← Category.assoc]
  exact Iso.inv_hom_id_assoc (pbPiIso (Curve.specMap K L) C.toOver n)
    (Work.SymQuot.proj ((Over.pullback (Curve.specMap K L)).obj C.toOver) n m)

/-- The same statement in the form in which it is consumed below, with `(C_L)` for the base
change. -/
theorem symPiIso_inv_map_proj (n : ℕ) (m : Fin n) :
    (symPiIso K L C n).inv ≫
        (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.proj C.toOver n m)
      = Work.SymQuot.proj (C.baseChange L).toOver n m :=
  pbPiIso_inv_map_proj (L := L) (C := C) n m

/-- **Naturality of `pbPtMap` in the scheme**: projecting a point of the base change after
composing with the base change of `u` is composing the projection of the point with `u`. -/
theorem pbPtMap_comp_pbMap {Y Y' : Work.GCBasics.Sch K} (u : Y ⟶ Y')
    (p : Work.SpecLin.FPt ((Over.pullback (Curve.specMap K L)).obj Y) F) :
    Work.BcDiv.pbPtMap (L := L) Y' (p ≫ (Over.pullback (Curve.specMap K L)).map u)
      = Work.BcDiv.pbPtMap (L := L) Y p ≫ u := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Work.BcDiv.pbPtMap_left, Over.pullback_map_left,
    Category.assoc, pullback.lift_fst]

/-- Projecting a point of `C_L` to a point of `C` is `projOfBaseChange`. -/
theorem pbPtMap_toOver_eq_bcPtK (x : Work.SpecLin.FPt (C.baseChange L).toOver F) :
    Work.BcDiv.pbPtMap (L := L) C.toOver x = Work.BcDiv.bcPtK (C := C) x :=
  Over.OverMorphism.ext rfl

/-- `projOfBaseChange` is `bcPtK`, the projection of a point of the base change. -/
theorem projOfBaseChange_eq_bcPtK (x : Work.SpecLin.FPt (C.baseChange L).toOver F) :
    projOfBaseChange (C := C) (L := L) x = Work.BcDiv.bcPtK (C := C) x :=
  Over.OverMorphism.ext rfl

/-- **The `n`-fold form of the projection of a base-change point**: the projection to `Cⁿ` of
the `n`-tuple of points of `C_L` is the `n`-tuple of the projected points. -/
theorem pbPtMap_lift (n : ℕ) (x : Fin n → Work.SpecLin.FPt (C.baseChange L).toOver F) :
    Work.BcDiv.pbPtMap (L := L) (Work.SymQuot.prod C.toOver n)
        (Limits.Pi.lift x ≫ (symPiIso K L C n).inv)
      = Limits.Pi.lift (fun m => projOfBaseChange (C := C) (L := L) (x m)) := by
  apply Limits.Pi.hom_ext
  intro m
  have hPm : (Limits.Pi.lift x ≫ (symPiIso K L C n).inv) ≫
      (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.proj C.toOver n m) = x m := by
    rw [Category.assoc, symPiIso_inv_map_proj]
    exact Limits.Pi.lift_comp_π x m
  rw [← pbPtMap_comp_pbMap (L := L) (u := Work.SymQuot.proj C.toOver n m)
        (p := Limits.Pi.lift x ≫ (symPiIso K L C n).inv)]
  rw [hPm, Limits.Pi.lift_comp_π, pbPtMap_toOver_eq_bcPtK, ← projOfBaseChange_eq_bcPtK]

end Helpers

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem powMap_symBeta {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] {n : ℕ} {L : Type u} [Field L] [Algebra K L]
    {F : Type u} [Field F] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
    (x : Fin n → Work.SpecLin.FPt (C.baseChange L).toOver F) :
    (Work.SymQuot.Sym.powMap (C.baseChange L) n x ≫ symβ K L C n).left ≫
        pullback.fst (Work.SymQuot.Sym C n).hom (Work.CurveBasics.Curve.specMap K L)
      = (Work.SymQuot.Sym.powMap C n
          (fun m => projOfBaseChange (C := C) (L := L) (x m))).left := by
  have hw : Work.SymQuot.Sym.powMap (C.baseChange L) n x ≫ symβ K L C n
      = (Limits.Pi.lift x ≫ (symPiIso K L C n).inv) ≫
          (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.Sym.quot C n) := by
    rw [Work.SymQuot.Sym.powMap, Category.assoc, symβ_spec, symfL, symqL, ← Category.assoc]
  calc
    (Work.SymQuot.Sym.powMap (C.baseChange L) n x ≫ symβ K L C n).left ≫
        pullback.fst (Work.SymQuot.Sym C n).hom (Curve.specMap K L)
        = ((Limits.Pi.lift x ≫ (symPiIso K L C n).inv) ≫
              (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.Sym.quot C n)).left ≫
            pullback.fst (Work.SymQuot.Sym C n).hom (Curve.specMap K L) := by rw [hw]
    _ = (Work.BcDiv.pbPtMap (L := L) (Work.SymQuot.Sym C n)
          ((Limits.Pi.lift x ≫ (symPiIso K L C n).inv) ≫
            (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.Sym.quot C n))).left := by
          rw [← Work.BcDiv.pbPtMap_left]
    _ = (Work.BcDiv.pbPtMap (L := L) (Work.SymQuot.prod C.toOver n)
            (Limits.Pi.lift x ≫ (symPiIso K L C n).inv) ≫
            Work.SymQuot.Sym.quot C n).left := by
          rw [pbPtMap_comp_pbMap]
    _ = (Limits.Pi.lift (fun m => projOfBaseChange (C := C) (L := L) (x m)) ≫
            Work.SymQuot.Sym.quot C n).left := by
          rw [pbPtMap_lift]
    _ = (Work.SymQuot.Sym.powMap C n
          (fun m => projOfBaseChange (C := C) (L := L) (x m))).left := by
          rw [Work.SymQuot.Sym.powMap]

end Work.SymQuot.BaseChange

/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.C6)
-/
import Submission.Work.JacClose.Inputs
import Submission.Work.JacFinal.All

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area JacClose — the concrete `k'`-level inputs of the final assembly

This file assembles the object the whole area is about: the `k'`-level inputs
`Work.JacFinal.Inputs C P0` of the final assembly, for a curve `C` over `k`, a base point `P0`
and the Galois-equivariant covering `D : Work.Charts.GalCharts C R P0` over `k`.

* `Work.JacClose.closeInputs` — the `Inputs`, whose chart datum is `gcInput` (C3) and whose
  exports are `upInput` (C4);
* `Work.JacClose.closeInputs_chart` / `closeInputs_exports` — the two `rfl`-lemmas identifying its
  fields with the builders;
* `Work.JacClose.closeData` — the `Work.JacFinal.Data`, from the two items of §1.4 (`IsAffineOpen
  V` and the class-level `Γ`-orbit statement, i.e. C6);
* `Work.JacClose.symGalBetaProp` — the *statement* of C5 as a `Prop`, in the exact form in which
  §2.C5 states it;
* `Work.JacClose.closeCovOrbitProp` — the statement of C6 (the class-level `Γ`-orbit statement
  for `closeInputs`), as a `Prop`.

## The `SymGeom` instance

Everything over `k'` is written with the *same* `SymGeom` instance as the one inside
`Work.JacClose.SYData` (`closeSymGeom` below).  This is what makes
`(closeInputs …).chart.Sym (closeInputs …).chart.g` definitionally the symmetric power
`Work.Charts.Sym (C_{k'}) R'.g` at which the comparison `B : Work.Charts.SymBC R D.k' R'`
starts, and hence makes `symGalBetaProp` and `closeCovOrbitProp` statable.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.JacClose

open Work.CurveBasics
open Work.GCBasics
open Work.GroupChunk (bcKF)

noncomputable section

variable {k : Type u} [Field k]
variable {C : Curve k} {P0 : Work.Charts.unitSch k ⟶ C.toOver}
variable {R : Work.Charts.RochData C} [Work.SpecLin.SymGeom C R.g] [NeZero R.g]
variable (D : Work.Charts.GalCharts C R P0)

/-- The base point of `C_{k'}` induced by `P0` (area `JacFinal`'s `bcPt`), for the extension
`k' = D.k'` of the Galois-equivariant covering `D`. -/
abbrev closePt : 𝟙_ (Work.GCBasics.Sch D.k') ⟶ (C.baseChange D.k').toOver :=
  Work.JacFinal.bcPt C P0 D.k'

/-! ## Abbreviations for the data of §2.C6 -/

variable {SG : ∀ n, Work.SpecLin.SymGeom (C.baseChange D.k') n}
  [sy : SYData (C.baseChange D.k') (closePt (C := C) (P0 := P0) D) SG]
  {R' : Work.Charts.RochData (C.baseChange D.k')} [NeZero R'.g]

/-- **The normality of `Sym^{R'.g}(C_{k'})`** (area `NM`, the first of the two fields that the
corrected RESID interface of area `GC` needs at the use site `X = D.Sym D.g`). -/
abbrev CloseNormalG : Prop :=
  ∀ x : ((SG R'.g).S).left,
    IsIntegrallyClosed (((SG R'.g).S).left.presheaf.stalk x)

/-- **The normality of `Sym^{R'.g}(C_{k'}) ⊗ Sym^{R'.g}(C_{k'})`** (area `NM`, the second of the
two fields, needed at `X = SymSym D`). -/
abbrev CloseNormalGG : Prop :=
  ∀ x : (((SG R'.g).S) ⊗ ((SG R'.g).S)).left,
    IsIntegrallyClosed ((((SG R'.g).S) ⊗ ((SG R'.g).S)).left.presheaf.stalk x)

/-- **A5 for the base point**: the divisor of the `F`-point `P0` is the base change of the
divisor of the `k'`-point `P0'`.  This is area `CurveFacts`'s `bcKF_ptDiv` at the base point
(`Work.JacFinal.bcPt`), taken at the level `k'`. -/
abbrev CloseP0Div : Prop :=
  ∀ {F : Type u} [Field F] [Algebra D.k' F],
    Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
        (closePt (C := C) (P0 := P0) D) F)
      = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (closePt (C := C) (P0 := P0) D) D.k'))

variable {cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _ R' (SG R'.g)
    (closePt (C := C) (P0 := P0) D)}
  {hresid : ResidOld (C.baseChange D.k') SG R'.g sy.isProper_Sym}
  {hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
    Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
        (closePt (C := C) (P0 := P0) D) F)
      = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (closePt (C := C) (P0 := P0) D) D.k'))}
  {hnorm_g : ∀ x : ((SG R'.g).S).left,
    IsIntegrallyClosed (((SG R'.g).S).left.presheaf.stalk x)}
  {hnorm_gg : ∀ x : (((SG R'.g).S) ⊗ ((SG R'.g).S)).left,
    IsIntegrallyClosed ((((SG R'.g).S) ⊗ ((SG R'.g).S)).left.presheaf.stalk x)}

/-- **C3 at the concrete `k'`-level**: the chart datum of area `GC` built by `gcInput`, under a
short name (so that the statements below do not have to spell out the term). -/
def gcInputOf (sy : SYData (C.baseChange D.k') (closePt (C := C) (P0 := P0) D) SG)
    (R' : Work.Charts.RochData (C.baseChange D.k')) [NeZero R'.g]
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _ R' (SG R'.g)
      (closePt (C := C) (P0 := P0) D))
    (hresid : ResidOld (C.baseChange D.k') SG R'.g sy.isProper_Sym)
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (closePt (C := C) (P0 := P0) D) F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (closePt (C := C) (P0 := P0) D) D.k')))
    (hnorm_g : ∀ x : ((SG R'.g).S).left,
      IsIntegrallyClosed (((SG R'.g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((SG R'.g).S) ⊗ ((SG R'.g).S)).left,
      IsIntegrallyClosed ((((SG R'.g).S) ⊗ ((SG R'.g).S)).left.presheaf.stalk x)) :
    GroupChunk.Input (C.baseChange D.k') (closePt (C := C) (P0 := P0) D) :=
  gcInput sy R' cd hresid hP0Div hnorm_g hnorm_gg

/-- **C4 at the concrete `k'`-level**: area `SY`'s quotient property for `gcInputOf`. -/
theorem symQuotDataOf (sy : SYData (C.baseChange D.k') (closePt (C := C) (P0 := P0) D) SG)
    (R' : Work.Charts.RochData (C.baseChange D.k')) [NeZero R'.g]
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _ R' (SG R'.g)
      (closePt (C := C) (P0 := P0) D))
    (hresid : ResidOld (C.baseChange D.k') SG R'.g sy.isProper_Sym)
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (closePt (C := C) (P0 := P0) D) F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (closePt (C := C) (P0 := P0) D) D.k')))
    (hnorm_g : ∀ x : ((SG R'.g).S).left,
      IsIntegrallyClosed (((SG R'.g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((SG R'.g).S) ⊗ ((SG R'.g).S)).left,
      IsIntegrallyClosed ((((SG R'.g).S) ⊗ ((SG R'.g).S)).left.presheaf.stalk x)) :
    @Work.Universal.SymQuotData D.k' _ (C.baseChange D.k') (closePt (C := C) (P0 := P0) D) _
      (gcInputOf D sy R' cd hresid hP0Div hnorm_g hnorm_gg) :=
  symQuotData sy R' cd hresid hP0Div hnorm_g hnorm_gg

/-- The key lemma of area `KL` for the concrete chart datum `gcInputOf`: the shape of the
hypothesis of `Work.JacClose.upInput`. -/
abbrev CloseKL (sy : SYData (C.baseChange D.k') (closePt (C := C) (P0 := P0) D) SG)
    (R' : Work.Charts.RochData (C.baseChange D.k')) [NeZero R'.g]
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _ R' (SG R'.g)
      (closePt (C := C) (P0 := P0) D))
    (hresid : ResidOld (C.baseChange D.k') SG R'.g sy.isProper_Sym)
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (closePt (C := C) (P0 := P0) D) F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (closePt (C := C) (P0 := P0) D) D.k')))
    (hnorm_g : ∀ x : ((SG R'.g).S).left,
      IsIntegrallyClosed (((SG R'.g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((SG R'.g).S) ⊗ ((SG R'.g).S)).left,
      IsIntegrallyClosed ((((SG R'.g).S) ⊗ ((SG R'.g).S)).left.presheaf.stalk x)) :
    Prop :=
  @KLLemma D.k' _ (C.baseChange D.k') (closePt (C := C) (P0 := P0) D) _
    (gcInputOf D sy R' cd hresid hP0Div hnorm_g hnorm_gg)
    (symQuotDataOf D sy R' cd hresid hP0Div hnorm_g hnorm_gg)

variable {hkl : CloseKL D sy R' cd hresid hP0Div hnorm_g hnorm_gg}

/-- **C6: the concrete inputs of the final assembly.**  From the `SY`-side data `sy` on `C_{k'}`,
the `RochData` `R'` over `k'`, area `CH`'s chart datum `cd`, area `DM`'s RESID datum, the
`divOf`-identity for the base point (area `CurveFacts`'s A5), the two normality fields (area `NM`
/ `CurveFacts` A4) and the key lemma (A6), the `k'`-level inputs of the final assembly, over the
Galois extension `D.k'`. -/
def closeInputs (sy : SYData (C.baseChange D.k') (closePt (C := C) (P0 := P0) D) SG)
    (R' : Work.Charts.RochData (C.baseChange D.k')) [NeZero R'.g]
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _ R' (SG R'.g)
      (closePt (C := C) (P0 := P0) D))
    (hresid : ResidOld (C.baseChange D.k') SG R'.g sy.isProper_Sym)
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (closePt (C := C) (P0 := P0) D) F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (closePt (C := C) (P0 := P0) D) D.k')))
    (hnorm_g : ∀ x : ((SG R'.g).S).left,
      IsIntegrallyClosed (((SG R'.g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((SG R'.g).S) ⊗ ((SG R'.g).S)).left,
      IsIntegrallyClosed ((((SG R'.g).S) ⊗ ((SG R'.g).S)).left.presheaf.stalk x))
    (hkl : CloseKL D sy R' cd hresid hP0Div hnorm_g hnorm_gg) :
    Work.JacFinal.Inputs C P0 :=
  { k' := D.k'
    field' := D.field'
    algebra' := D.algebra'
    galois' := D.galois
    finiteDimensional' := D.finiteDimensional
    chart := gcInputOf D sy R' cd hresid hP0Div hnorm_g hnorm_gg
    exports := upInput sy R' cd hresid hP0Div hnorm_g hnorm_gg hkl }

/-- The chart datum of `closeInputs` is the builder `gcInput` of C3. -/
theorem closeInputs_chart : (closeInputs D sy R' cd hresid hP0Div hnorm_g hnorm_gg hkl).chart
    = gcInputOf D sy R' cd hresid hP0Div hnorm_g hnorm_gg := rfl

/-- The exports of `closeInputs` are the builder `upInput` of C4. -/
theorem closeInputs_exports :
    (closeInputs D sy R' cd hresid hP0Div hnorm_g hnorm_gg hkl).exports
      = upInput sy R' cd hresid hP0Div hnorm_g hnorm_gg hkl := rfl

/-- **C6/C7: the `Data` of the final assembly**, from the two items of §1.4 in the form
`Work.JacFinal.Inputs.CovOrbit`: `IsAffineOpen V` (the lead's (G1)) and the class-level
`Γ`-orbit statement (the lead's (G2)/(f), the output of C5 + C6). -/
def closeData (h : Work.JacFinal.Inputs.CovOrbit
    (closeInputs D sy R' cd hresid hP0Div hnorm_g hnorm_gg hkl)) :
    Work.JacFinal.Data C P0 :=
  Work.JacFinal.Data.of_covOrbit (closeInputs D sy R' cd hresid hP0Div hnorm_g hnorm_gg hkl) h

/-- Area `CH`'s `IsAffineOpen V` for the chart datum of `closeInputs` (the lead's (G1)). -/
theorem closeData_hV (h : Work.JacFinal.Inputs.CovOrbit
    (closeInputs D sy R' cd hresid hP0Div hnorm_g hnorm_gg hkl)) :
    IsAffineOpen (gcInputOf D sy R' cd hresid hP0Div hnorm_g hnorm_gg).V :=
  h.hV

/-! ## The statements of C5 and C6 -/

/-- The symmetric power `Sym^{R'.g}(C_{k'})` of the `SY`-data `sy`: the source of the comparison
`B` of symmetric powers. -/
abbrev closeSymPower : Work.GCBasics.Sch D.k' := (SG R'.g).S

/-- The concrete inputs of the final assembly, under a short name (`def`, so that the statements
below can mention it without unfolding the whole builder). -/
def closeIn (sy : SYData (C.baseChange D.k')
      (closePt (C := C) (P0 := P0) D) SG)
    (R' : Work.Charts.RochData (C.baseChange D.k')) [NeZero R'.g]
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _ R' (SG R'.g)
      (closePt (C := C) (P0 := P0) D))
    (hresid : ResidOld (C.baseChange D.k') SG R'.g sy.isProper_Sym)
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (closePt (C := C) (P0 := P0) D) F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (closePt (C := C) (P0 := P0) D) D.k')))
    (hnorm_g : ∀ x : ((SG R'.g).S).left,
      IsIntegrallyClosed (((SG R'.g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((SG R'.g).S) ⊗ ((SG R'.g).S)).left,
      IsIntegrallyClosed ((((SG R'.g).S) ⊗ ((SG R'.g).S)).left.presheaf.stalk x))
    (hkl : CloseKL D sy R' cd hresid hP0Div hnorm_g hnorm_gg) :
    Work.JacFinal.Inputs C P0 :=
  closeInputs D sy R' cd hresid hP0Div hnorm_g hnorm_gg hkl


end

end Work.JacClose

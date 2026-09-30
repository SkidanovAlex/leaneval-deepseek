/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.C6)
-/
import Submission.Work.JacClose.Close
import Submission.Work.BNChart.All

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area JacClose — C5/C6 in the successor shape (`RochData` of `BNChart`)

The chart datum of area `GC` built by `Work.JacClose.gcInput` on the one hand, and the
comparison of symmetric powers `Work.BcDiv.symBC` on the other, carry *different* `SymGeom`
instances unless the genus is written in the successor shape `(genus C - 1) + 1` and the
family is the concrete `Work.SymQuot.symGeomFamily`: `Work.Charts.Sym` is an `abbrev` whose body
is `(inferInstance).S`, so the elaborator re-synthesizes `instSymGeomOfNeZero` at every unfold
site, while `gcInput` uses the family it was given.  The two are *definitionally equal* once the
genus is a syntactic successor, because then `symGeomFamily C ((genus C - 1) + 1)` reduces to
`instSymGeomOfNeZero C ((genus C - 1) + 1)` by `whnf` — this is rule (D4) of the lead's design.

This file therefore instantiates everything with

* `R := Work.BNChart.rochDataPos C h` (the successor-shaped `RochData` of area `BNChart`, B1),
* `R' := Work.BNChart.rochDataPos (C_{k'}) h'`,
* `sg := Work.SymQuot.symGeomFamily` (the concrete family),

so that the statements of C5 and C6 — which mention both `B.β` (or `B.pts`) and the chart of
`gcInput` — are well-typed.
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

open Work.CurveBasics Work.GCBasics
open Work.GroupChunk (bcKF)

noncomputable section

variable {k : Type u} [Field k]
variable {C : Curve k} {P0 : Work.Charts.unitSch k ⟶ C.toOver}
variable (h : RiemannRoch.Curve.genus C ≠ 0)

/-- The base point of `C_{k'}` for the extension of the covering `D`. -/
abbrev posPt (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0) :
    𝟙_ (Work.GCBasics.Sch D.k') ⟶ (C.baseChange D.k').toOver :=
  Work.JacFinal.bcPt C P0 D.k'

/-- The concrete inputs of the final assembly in the successor shape: the `RochData` of area
`BNChart` (B1) on both sides, the family `SymQuot.symGeomFamily`, and a chart datum `cd` over
`k'` whose `SymGeom` instance is `symGeomFamily (C_{k'}) R'.g` (definitionally
`instSymGeomOfNeZero`). -/
abbrev posInputs (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0)
    (h' : RiemannRoch.Curve.genus (C.baseChange D.k') ≠ 0)
    (sy : SYData (C.baseChange D.k') (posPt (C := C) (P0 := P0) h D)
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')))
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      (posPt (C := C) (P0 := P0) h D))
    (hresid : ResidOld (C.baseChange D.k') (Work.SymQuot.symGeomFamily (C.baseChange D.k'))
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g
      (sy.isProper_Sym))
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (posPt (C := C) (P0 := P0) h D) F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (posPt (C := C) (P0 := P0) h D) D.k')))
    (hnorm_g : ∀ x : ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S).left,
      IsIntegrallyClosed (((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ⊗ ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left,
      IsIntegrallyClosed ((((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ⊗ ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left.presheaf.stalk x))
    (hkl : CloseKL D sy (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid
      hP0Div hnorm_g hnorm_gg) :
    Work.JacFinal.Inputs C P0 :=
  closeIn D sy (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid hP0Div
    hnorm_g hnorm_gg hkl



/-- **The canonical comparison of symmetric powers** (area `BcDiv`, B7) for the successor-shaped
`RochData`: `Work.BcDiv.symBC`.  Unlike a general `Work.Charts.SymBC` bundle, this one *is*
pinned by the quotient maps (`Work.SymQuot.BaseChange.symβ_spec`), which is what C5 needs. -/
def posCanonBC (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0)
    (h' : Work.RiemannRoch.Curve.genus (C.baseChange D.k') ≠ 0)
    (hg : (Work.BNChart.rochDataPos (C.baseChange D.k') h').g
      = (Work.BNChart.rochDataPos C h).g)
    (Q' : (C.baseChange D.k').Place) (U' : (C.baseChange D.k').left.Opens)
    (hU' : IsAffineOpen U')
    (hb : Fin (Work.BNChart.rochDataPos (C.baseChange D.k') h').g →
      ((C.baseChange D.k').baseChange D.k').functionField)
    (h_mem : ∀ j, (0 : ((C.baseChange D.k').baseChange D.k').Div)
      ≤ ((C.baseChange D.k').baseChange D.k').div (hb j)
        + (Work.BNChart.rochDataPos (C.baseChange D.k') h').W)
    (h_span : ((C.baseChange D.k').baseChange D.k').L
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').W
      = Submodule.span D.k' (Set.range hb)) :
    Work.Charts.SymBC (Work.BNChart.rochDataPos C h) D.k'
      (Work.BNChart.rochDataPos (C.baseChange D.k') h') :=
  Work.BcDiv.symBC (Work.BNChart.rochDataPos C h)
    (Work.BNChart.rochDataPos (C.baseChange D.k') h') hg Q' U' hU' hb h_mem h_span

/-- **The chart datum `cd` is the base change of the Brill–Noether chart of `D` along `B`** (C2):
`cd = (D.chartsK' B).toChartDatum`, so that its chart is `B.β ⁻¹ᵁ D.d.V` and its centres are
`B.pts.symm ∘ D.E`.  In the concrete setting this holds by `rfl`
(`Work.Charts.GalCharts.chartsK'_V`, `chartsK'_E`); it is the linkage that ties the chart of
`posInputs` to the comparison `B` and makes C5/C6 provable (C5's route uses
`BcDiv.powMap_betaK`/`symβ_spec`, lemmas about the *concrete* comparison). -/
def posChartEq (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0)
    (h' : Work.RiemannRoch.Curve.genus (C.baseChange D.k') ≠ 0)
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      (posPt (C := C) (P0 := P0) h D))
    (B : Work.Charts.SymBC (Work.BNChart.rochDataPos C h) D.k'
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')) : Prop :=
  cd = (D.chartsK' (Work.SymQuot.instDivBase (C.baseChange D.k'))
    (Work.BNChart.rochDataPos (C.baseChange D.k') h')
    (Work.SymQuot.symGeomFamily (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
    (posPt (C := C) (P0 := P0) h D) B).toChartDatum

/-- **The statement of C5** (§2.C5) in the successor shape: `τ_σ` commutes with the comparison
`β` of symmetric powers, `(symGal σ).left ≫ B.β = B.β`. -/
def posSymGalBetaProp (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0)
    (h' : RiemannRoch.Curve.genus (C.baseChange D.k') ≠ 0)
    (sy : SYData (C.baseChange D.k') (posPt (C := C) (P0 := P0) h D)
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')))
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      (posPt (C := C) (P0 := P0) h D))
    (hresid : ResidOld (C.baseChange D.k') (Work.SymQuot.symGeomFamily (C.baseChange D.k'))
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g (sy.isProper_Sym))
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (posPt (C := C) (P0 := P0) h D) F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (posPt (C := C) (P0 := P0) h D) D.k')))
    (hnorm_g : ∀ x : ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S).left,
      IsIntegrallyClosed (((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ⊗ ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left,
      IsIntegrallyClosed ((((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ⊗ ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left.presheaf.stalk x))
    (hkl : CloseKL D sy (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid
      hP0Div hnorm_g hnorm_gg)
    (B : Work.Charts.SymBC (Work.BNChart.rochDataPos C h) D.k'
      (Work.BNChart.rochDataPos (C.baseChange D.k') h'))
    (σ : Work.Descent.Gal k D.k') : Prop :=
  ((posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg hkl).symGal σ).left
    ≫ B.β = B.β

/-- **The statement of C6** (§2.C6) in the successor shape: the class-level `Γ`-orbit statement
for the concrete inputs `posInputs`. -/
def posCovOrbitProp (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0)
    (h' : RiemannRoch.Curve.genus (C.baseChange D.k') ≠ 0)
    (sy : SYData (C.baseChange D.k') (posPt (C := C) (P0 := P0) h D)
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')))
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      (posPt (C := C) (P0 := P0) h D))
    (hresid : ResidOld (C.baseChange D.k') (Work.SymQuot.symGeomFamily (C.baseChange D.k'))
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g (sy.isProper_Sym))
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (posPt (C := C) (P0 := P0) h D) F)
        = bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (posPt (C := C) (P0 := P0) h D) D.k')))
    (hnorm_g : ∀ x : ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S).left,
      IsIntegrallyClosed (((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S).left.presheaf.stalk x))
    (hnorm_gg : ∀ x : (((Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ⊗ ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left,
      IsIntegrallyClosed ((((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ⊗ ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left.presheaf.stalk x))
    (hkl : CloseKL D sy (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid
      hP0Div hnorm_g hnorm_gg) : Prop :=
  ∀ x : (posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg hkl).toChunk.G.left,
    ∃ i : (posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
        hnorm_gg hkl).chart.Idx,
      ∀ σ : Work.Descent.Gal k D.k',
        (posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg
            hkl).chart.InChart i
          ((posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg
              hkl).exports.glued.cls
            (Work.GCBasics.resPt
              (posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg
                hkl).toChunk.G
              (((posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg
                hkl).toChunk.galAct σ).hom x)))

end

end Work.JacClose

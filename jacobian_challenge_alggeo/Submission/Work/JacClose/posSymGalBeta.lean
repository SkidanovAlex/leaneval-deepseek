import Mathlib
import Submission.Work.JacClose.ClosePos
import Submission.Work.BcDiv.symquot_comp_betaK
import Submission.Work.JacFinal.galProd_comp_symPiIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



namespace Work.JacClose

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

variable {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
  {P0 : Work.Charts.unitSch k ⟶ C.toOver}
variable (h : Work.RiemannRoch.Curve.genus C ≠ 0)

theorem posSymGalBeta (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0)
    (h' : Work.RiemannRoch.Curve.genus (C.baseChange D.k') ≠ 0)
    (sy : Work.JacClose.SYData (C.baseChange D.k') (Work.JacClose.posPt (C := C) (P0 := P0) h D)
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')))
    (cd : @Work.Charts.ChartDatum D.k' _ (C.baseChange D.k') _
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      (Work.JacClose.posPt (C := C) (P0 := P0) h D))
    (hresid : Work.JacClose.ResidOld (C.baseChange D.k')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k'))
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g (sy.isProper_Sym))
    (hP0Div : ∀ {F : Type u} [Field F] [Algebra D.k' F],
      Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (Work.JacClose.posPt (C := C) (P0 := P0) h D) F)
        = Work.GroupChunk.bcKF F (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (Work.JacClose.posPt (C := C) (P0 := P0) h D) D.k')))
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
    (hkl : Work.JacClose.CloseKL D sy (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid
      hP0Div hnorm_g hnorm_gg)
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
      = Submodule.span D.k' (Set.range hb))
    (hcd : Work.JacClose.posChartEq (C := C) (P0 := P0) h D h' cd
      (Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hg Q' U' hU' hb h_mem h_span))
    (σ : Work.Descent.Gal k D.k') :
    Work.JacClose.posSymGalBetaProp (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
      hnorm_gg hkl (Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hg Q' U' hU' hb h_mem
        h_span) σ := by
  -- The concrete inputs and the concrete comparison.
  let d : Work.JacFinal.Inputs C P0 :=
    Work.JacClose.posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg hkl
  let B : Work.Charts.SymBC (Work.BNChart.rochDataPos C h) D.k'
      (Work.BNChart.rochDataPos (C.baseChange D.k') h') :=
    Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hg Q' U' hU' hb h_mem h_span
  change (d.symGal σ).left ≫ B.β = B.β
  -- The comparison `(C_{k'})^g ⟶ C^g` of area `BcDiv`.
  let PI : (Work.SymQuot.prod (C.baseChange d.k').toOver d.chart.g).left
      ⟶ (Work.SymQuot.prod C.toOver d.chart.g).left :=
    (Work.SymQuot.BaseChange.symPiIso k d.k' C d.chart.g).inv.left
      ≫ pullback.fst (Work.SymQuot.prod C.toOver d.chart.g).hom
          (Work.CurveBasics.Curve.specMap k d.k')
  -- ## 0. The value of `B.β`
  have hβexp : B.β = Work.BcDiv.βK (K := k) (L := d.k') (C := C) d.chart.g
      ≫ (eqToIso (congrArg (fun m => Work.SymQuot.Sym C m) hg)).hom.left := rfl
  -- ## 1. The quotient map of `Sym^g C_{k'}` is the concrete `Sym.quot`
  have hquot : (d.quotMapC d.chart.g).left
      = (Work.SymQuot.Sym.quot (C.baseChange d.k') d.chart.g).left := by
    show (Work.SymQuot.Sym.powMap (C.baseChange d.k') d.chart.g
        (fun m => d.projC d.chart.g m)).left = _
    rw [Work.SymQuot.Sym.powMap, Over.comp_left]
    rw [show (Limits.Pi.lift (fun m : Fin d.chart.g => d.projC d.chart.g m)).left
        = 𝟙 (d.prodC d.chart.g).left from by
      rw [← Over.id_left, congrArg Over.Hom.left (Limits.Pi.lift_π (f := fun _ : Fin d.chart.g => d.C'))]]
    rw [Category.id_comp]
  -- ## 2. `symGal` on the quotient
  have hA : (d.quotMapC d.chart.g).left ≫ (d.symGal σ).left
      = (d.galProd σ d.chart.g).left ≫ (d.quotMapC d.chart.g).left := by
    have h := congrArg Over.Hom.left (Work.JacFinal.Inputs.symGal_spec d σ)
    simpa only [Over.comp_left, Over.map_map_left, Work.JacFinal.Gal.tw] using h
  -- ## 3. `Sym.quot` followed by `β` is `PI` followed by the quotient of `C`
  have hβ : (Work.SymQuot.Sym.quot (C.baseChange d.k') d.chart.g).left ≫ B.β
      = PI ≫ ((Work.SymQuot.Sym.quot C d.chart.g).left
              ≫ (eqToIso (congrArg (fun m => Work.SymQuot.Sym C m) hg)).hom.left) := by
    rw [hβexp, ← Category.assoc, Work.BcDiv.symquot_comp_betaK, Category.assoc]
  -- ## 4. The diagonal action is killed by the product projection
  have hPi : (d.galProd σ d.chart.g).left ≫ PI = PI :=
    Work.JacFinal.galProd_comp_symPiIso d d.chart.g σ
  -- ## 5. The quotient map is dominant
  haveI hred : IsReduced ((d.chart.symGeom d.chart.g).S).left :=
    Work.GroupChunk.Input.instIsReduced d.chart d.chart.g
  haveI hdom : IsDominant (d.quotMapC d.chart.g).left := by
    rw [hquot]
    exact IsDominant.mk (Work.SymQuot.Sym.quot_surjective (C.baseChange d.k') d.chart.g).denseRange
  -- ## 6. Conclusion
  exact AlgebraicGeometry.ext_of_isDominant (ι := (d.quotMapC d.chart.g).left) (by
    calc (d.quotMapC d.chart.g).left ≫ ((d.symGal σ).left ≫ B.β)
        = ((d.quotMapC d.chart.g).left ≫ (d.symGal σ).left) ≫ B.β := by rw [Category.assoc]
      _ = ((d.galProd σ d.chart.g).left ≫ (d.quotMapC d.chart.g).left) ≫ B.β := by rw [hA]
      _ = (d.galProd σ d.chart.g).left
            ≫ ((d.quotMapC d.chart.g).left ≫ B.β) := by rw [Category.assoc]
      _ = (d.galProd σ d.chart.g).left
            ≫ ((Work.SymQuot.Sym.quot (C.baseChange d.k') d.chart.g).left ≫ B.β) := by
            rw [hquot]
      _ = (d.galProd σ d.chart.g).left
            ≫ (PI ≫ ((Work.SymQuot.Sym.quot C d.chart.g).left
                ≫ (eqToIso (congrArg (fun m => Work.SymQuot.Sym C m) hg)).hom.left)) := by
            rw [hβ]
      _ = ((d.galProd σ d.chart.g).left ≫ PI)
            ≫ ((Work.SymQuot.Sym.quot C d.chart.g).left
                ≫ (eqToIso (congrArg (fun m => Work.SymQuot.Sym C m) hg)).hom.left) := by
            rw [← Category.assoc]
      _ = PI ≫ ((Work.SymQuot.Sym.quot C d.chart.g).left
              ≫ (eqToIso (congrArg (fun m => Work.SymQuot.Sym C m) hg)).hom.left) := by
            rw [hPi]
      _ = (Work.SymQuot.Sym.quot (C.baseChange d.k') d.chart.g).left ≫ B.β := hβ.symm
      _ = (d.quotMapC d.chart.g).left ≫ B.β := by rw [hquot])

end Work.JacClose

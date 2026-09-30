import Mathlib
import Submission.Work.JacClose.ClosePos
import Submission.Work.JacClose.posSymGalBeta
import Submission.Work.JacClose.posCovOrbitAux
import Submission.Work.JacClose.posCovOrbitHorbit

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

/-- **C6: the class-level `Γ`-orbit statement** for the concrete `k'`-level inputs
`Work.JacClose.posInputs` (`Work.JacClose.posCovOrbitProp`, i.e. the `hcov` field of
`Work.JacFinal.Inputs.CovOrbit`), deduced from the chart-range form
`Work.JacClose.posCovOrbitHorbit` (§1.4(f), the output of C5 + C6) through the chart/class
dictionary `Work.JacClose.inChart_of_mem_chartRange`. -/
theorem posCovOrbit (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0)
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
      (Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hg Q' U' hU' hb h_mem h_span)) :
    Work.JacClose.posCovOrbitProp (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
      hnorm_gg hkl := by
  intro x
  have hsgb : ∀ σ : Work.Descent.Gal k D.k',
      Work.JacClose.posSymGalBetaProp (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
        hnorm_gg hkl (Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hg Q' U' hU' hb h_mem
          h_span) σ :=
    fun σ => posSymGalBeta (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg hkl
      hg Q' U' hU' hb h_mem h_span hcd σ
  obtain ⟨i, hi⟩ := posCovOrbitHorbit (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
    hnorm_gg hkl hg Q' U' hU' hb h_mem h_span hsgb hcd x
  exact ⟨i, fun σ => inChart_of_mem_chartRange
    (Work.JacClose.posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g hnorm_gg
      hkl) (((Work.JacClose.posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
        hnorm_gg hkl).toChunk.galAct σ).hom x) i (hi σ)⟩

end Work.JacClose

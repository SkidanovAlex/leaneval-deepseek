import Mathlib
import Submission.Work.JacClose.ClosePos
import Submission.Work.JacClose.posCovOrbitAux
import Submission.Work.JacClose.bcPtK_P0Pt
import Submission.Work.BcDiv.pic0Map_picAJ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.synthInstance.canonInstances false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.JacClose

theorem posCovOrbitHorbit {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    {P0 : Work.Charts.unitSch k ⟶ C.toOver} (h : Work.RiemannRoch.Curve.genus C ≠ 0)
    (D : Work.Charts.GalCharts C (Work.BNChart.rochDataPos C h) P0)
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
    (hnorm_gg : ∀ x : (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left,
      IsIntegrallyClosed ((CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)
        ((Work.SymQuot.symGeomFamily (C.baseChange D.k')
          (Work.BNChart.rochDataPos (C.baseChange D.k') h').g).S)).left.presheaf.stalk x))
    (hkl : Work.JacClose.CloseKL D sy (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd hresid
      hP0Div hnorm_g hnorm_gg)
    (hg : (Work.BNChart.rochDataPos (C.baseChange D.k') h').g
      = (Work.BNChart.rochDataPos C h).g)
    (Q' : (C.baseChange D.k').Place) (U' : (C.baseChange D.k').left.Opens)
    (hU' : AlgebraicGeometry.IsAffineOpen U')
    (hb : Fin (Work.BNChart.rochDataPos (C.baseChange D.k') h').g →
      ((C.baseChange D.k').baseChange D.k').functionField)
    (h_mem : ∀ j, (0 : ((C.baseChange D.k').baseChange D.k').Div)
      ≤ ((C.baseChange D.k').baseChange D.k').div (hb j)
        + (Work.BNChart.rochDataPos (C.baseChange D.k') h').W)
    (h_span : ((C.baseChange D.k').baseChange D.k').L
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').W
      = Submodule.span D.k' (Set.range hb))
    (hsgb : ∀ σ : Work.Descent.Gal k D.k',
      Work.JacClose.posSymGalBetaProp (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
        hnorm_gg hkl (Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hg Q' U' hU' hb h_mem
          h_span) σ)
    (hcd : Work.JacClose.posChartEq (C := C) (P0 := P0) h D h' cd
      (Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hg Q' U' hU' hb h_mem h_span)) :
    ∀ x : (Work.JacClose.posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
        hnorm_gg hkl).toChunk.G.left,
      ∃ i : (Work.JacClose.posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
          hnorm_gg hkl).chart.Idx,
        ∀ σ : Work.Descent.Gal k D.k',
          ((Work.JacClose.posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
            hnorm_gg hkl).toChunk.galAct σ).hom x
            ∈ (Work.JacClose.posInputs (C := C) (P0 := P0) h D h' sy cd hresid hP0Div hnorm_g
              hnorm_gg hkl).chartRange i  := by
  let B : Work.Charts.SymBC (Work.BNChart.rochDataPos C h) D.k'
      (Work.BNChart.rochDataPos (C.baseChange D.k') h') :=
    Work.JacClose.posCanonBC (C := C) (P0 := P0) h D h' hg Q' U' hU' hb h_mem h_span
  -- `d` is written as the *structure literal* (rather than via `posInputs`) so that its
  -- instance fields are syntactically `D`'s: this is what keeps the `k'`-flavours aligned.
  let d : Work.JacFinal.Inputs C P0 :=
    { k' := D.k'
      field' := D.field'
      algebra' := D.algebra'
      galois' := D.galois
      finiteDimensional' := D.finiteDimensional
      chart := Work.JacClose.gcInput sy (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd
        hresid hP0Div hnorm_g hnorm_gg
      exports := Work.JacClose.upInput sy (Work.BNChart.rochDataPos (C.baseChange D.k') h') cd
        hresid hP0Div hnorm_g hnorm_gg hkl }
  subst hcd
  change ∀ x : d.toChunk.G.left, ∃ i : d.chart.Idx,
      ∀ σ : Work.Descent.Gal k (d.k'), (d.toChunk.galAct σ).hom x ∈ d.chartRange i
  have hidx : d.chart.Idx = D.ι := rfl
  have d3 : (Work.Charts.Sym (C.baseChange D.k') (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      = (d.chart.Sym d.chart.g) := rfl
  intro x
  -- The main step of C6, over an *opaque* field `F` (so that the local instance
  -- `Algebra k' F` can be shadowed by its Galois twist below).
  have key : ∀ (F : Type u) [Field F] [arr : Algebra (d.k') F]
      (q : Work.GCBasics.FPt (d.chart.Sym d.chart.g) F)
      (hs : (d.exports.AJSym).left (q.left (IsLocalRing.closedPoint F)) = x),
      ∃ i : D.ι, ∀ σ : Work.Descent.Gal k (d.k'),
        (d.toChunk.galAct σ).hom x ∈ d.chartRange i := by
    intro F _ arr q hs
    letI : Algebra D.k' F := arr
    letI : Algebra (d.k') F := arr
    letI : Work.GroupChunk.Input (C.baseChange D.k')
      (Work.JacClose.posPt (C := C) (P0 := P0) h D) := d.chart
    letI : Work.SpecLin.SymGeom (C.baseChange D.k')
      (Work.BNChart.rochDataPos (C.baseChange D.k') h').g :=
      Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g
    letI : Work.SpecLin.SymGeom (C.baseChange (d.k')) d.chart.g :=
      Work.SymQuot.symGeomFamily (C.baseChange (d.k')) d.chart.g
    letI : Algebra k F := Work.BcDiv.compAlgebra k (d.k') F
    haveI : IsScalarTower k (d.k') F := Work.BcDiv.isScalarTower_compAlgebra k (d.k') F
    haveI : IsScalarTower k D.k' F := ‹IsScalarTower k (d.k') F›
    let ε : (d.k') →ₐ[k] F := IsScalarTower.toAlgHom k (d.k') F
    let εD : D.k' →ₐ[k] F := ε
    let bq : Work.GCBasics.FPt (Work.Charts.Sym C (Work.BNChart.rochDataPos C h).g) F := B.pts q
    have hbq : bq.left = q.left ≫ B.β := B.pts_left q
    -- The base-point compatibility of the comparison `B` (B3 + the base point of `C_L`).
    have hP0_B : ∀ {F' : Type u} [Field F'] [Algebra D.k' F'] [Algebra k F']
        [IsScalarTower k D.k' F'],
        B.bcDiv (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
            (Work.JacClose.posPt (C := C) (P0 := P0) h D) F'))
          = Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F') := by
      intro F' _ _ _ _
      exact (Work.BcDiv.bcDiv_ptDiv (Work.Universal.P0Pt (C.baseChange D.k')
          (Work.JacClose.posPt (C := C) (P0 := P0) h D) F')).trans
        (congrArg Work.SpecLin.ptDiv
          (Work.JacClose.bcPtK_P0Pt (K := k) (C := C) (L := D.k') (F := F') P0))
    -- `hP0Div` re-read in the `d.k'`-flavour (the two are definitionally equal).
    have hP0Div_d : ∀ {F' : Type u} [Field F'] [Algebra (d.k') F'],
        Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange (d.k'))
            (Work.JacClose.posPt (C := C) (P0 := P0) h D) F')
          = Work.GroupChunk.bcKF F' (Work.SpecLin.ptDiv (Work.Universal.P0Pt
              (C.baseChange (d.k')) (Work.JacClose.posPt (C := C) (P0 := P0) h D)
              (d.k'))) :=
      fun {F'} _ _ => hP0Div (F := F')
    -- The general computation: pushing `B.pic0Map` through `picAJ` gives the class of
    -- `divOf (B.pts p) - g·[P0]` on `C`.
    have hexp : ∀ {F' : Type u} [Field F'] [alg : Algebra (d.k') F'] [algD : Algebra D.k' F']
        [algk : Algebra k F'] [stD : IsScalarTower k D.k' F']
        (p : Work.GCBasics.FPt (d.chart.Sym d.chart.g) F'),
        B.pic0Map (d.chart.picAJ p)
          = Work.GCBasics.Pic0.mk (Work.SpecLin.SymGeom.divOf (B.pts (F := F') p)
              - ((Work.BNChart.rochDataPos C h).g : ℤ) •
                Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F'))
            (by rw [map_sub, map_zsmul,
                  show (Work.GCBasics.Ddeg C F')
                      (Work.SpecLin.SymGeom.divOf (B.pts (F := F') p))
                    = ((Work.BNChart.rochDataPos C h).g : ℤ)
                    from (inferInstance : Work.SpecLin.SymGeom C
                      (Work.BNChart.rochDataPos C h).g).divOf_deg (B.pts (F := F') p),
                  show (Work.GCBasics.Ddeg C F')
                      (Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F')) = 1
                    from Work.SpecLin.Points.ptDiv_deg _]
                simp) := by
      intro F' _ alg algD algk stD p
      have h0 : d.chart.picAJ p = Work.GCBasics.Pic0.mk
          (d.chart.divOf d.chart.g p
            - Work.GroupChunk.bcKF F' (Work.GroupChunk.Input.P0g d.chart)) _ := rfl
      have hbp : B.bcDiv (Work.GroupChunk.bcKF F' (Work.GroupChunk.Input.P0g d.chart))
          = ((Work.BNChart.rochDataPos C h).g : ℤ) •
              Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F') := by
        have hpin : Work.SpecLin.DivBase.bc (Algebra.ofId (d.k') F') d.chart.P0Div
            = Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange (d.k'))
                (Work.JacClose.posPt (C := C) (P0 := P0) h D) F') :=
          (hP0Div_d (F' := F')).symm
        rw [show Work.GroupChunk.Input.P0g d.chart
              = d.chart.g • d.chart.P0Div from rfl,
          show Work.GroupChunk.bcKF F' (d.chart.g • d.chart.P0Div)
            = Work.SpecLin.DivBase.bc (Algebra.ofId (d.k') F')
                (d.chart.g • d.chart.P0Div) from rfl,
          Work.JacClose.bc_nsmul, map_nsmul, hpin, hP0_B,
          show d.chart.g = (Work.BNChart.rochDataPos C h).g from hg]
        rfl
      have hpts : B.bcDiv (d.chart.divOf d.chart.g p)
          = Work.SpecLin.SymGeom.divOf (B.pts (F := F') p) := B.pts_divOf p
      rw [h0, B.pic0Map_mk, Work.GCBasics.Pic0.mk_eq_iff, map_sub, hpts, hbp]
      exact Work.GCBasics.LinEquiv.refl _
    let c₀ : Work.GCBasics.Pic0 C F :=
      B.pic0Map (Work.GroupChunk.Input.picAJ d.chart q)
    have harr : c₀ = Work.GCBasics.Pic0.mk
        (Work.SpecLin.SymGeom.divOf bq
          - ((Work.BNChart.rochDataPos C h).g : ℤ) •
            Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F))
        (by rw [map_sub, map_zsmul,
              show (Work.GCBasics.Ddeg C F)
                  (Work.SpecLin.SymGeom.divOf bq)
                = ((Work.BNChart.rochDataPos C h).g : ℤ)
                from (inferInstance : Work.SpecLin.SymGeom C
                  (Work.BNChart.rochDataPos C h).g).divOf_deg bq,
              show (Work.GCBasics.Ddeg C F)
                  (Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F)) = 1
                from Work.SpecLin.Points.ptDiv_deg _]
            simp) :=
      hexp (F' := F) q
    obtain ⟨i, hi⟩ := D.orbit_cov εD c₀
    let ρo : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (d.k')) :=
      (Work.GCBasics.specOf (d.k') F).hom
    have hq : q.left ≫ (d.chart.Sym d.chart.g).hom = ρo := Over.w q
    have hρ : ρo = Spec.map (CommRingCat.ofHom ((algebraMap (d.k') F) : (d.k') →+* F)) := rfl
    have hε : ((ε : (d.k') →+* F)) = algebraMap (d.k') F := by
      ext y
      exact IsScalarTower.toAlgHom_apply k (d.k') F y
    refine ⟨i, fun σ => ?_⟩
    let σD : Work.Descent.Gal k D.k' := σ
    let εσ : (d.k') →ₐ[k] F := ε.comp σ.toAlgHom
    let εσD : D.k' →ₐ[k] F := εσ
    letI : Algebra D.k' F := εσ.toAlgebra
    letI : Algebra (d.k') F := εσ.toAlgebra
    haveI hST : IsScalarTower k (d.k') F := by
      refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
      change ε (algebraMap k (d.k') a) = εσ (algebraMap k (d.k') a)
      dsimp only [εσ, AlgHom.comp_apply]
      exact (congrArg ε (AlgEquiv.commutes σ a)).symm
    haveI hSTD : IsScalarTower k D.k' F := hST
    -- the twisted `F`-point of `Sym^g C_{k'}`
    let qσ : @Work.GCBasics.FPt (d.k') d.field' (d.chart.Sym d.chart.g) F
        (inferInstance : Field F) (εσ.toAlgebra) :=
      Over.homMk (q.left ≫ (d.symGal σ).left) (by
        have hsym : (d.symGal σ).left ≫ (d.chart.Sym d.chart.g).hom
            = (d.chart.Sym d.chart.g).hom ≫ Work.DescentGeom.specGal σ := by
          have h := Over.w (d.symGal σ)
          rw [show ((Work.JacFinal.Gal.tw σ).obj (d.chart.Sym d.chart.g)).hom
              = (d.chart.Sym d.chart.g).hom ≫ (Work.JacFinal.Gal.specGalIso σ).hom
            from CategoryTheory.Over.map_obj_hom] at h
          have h2 := congrArg (fun t => t ≫ Work.DescentGeom.specGal σ) h
          simp only [Category.assoc, Work.JacFinal.Gal.specGalIso,
            ← Work.DescentGeom.specGal_mul, inv_mul_cancel, Work.DescentGeom.specGal_one] at h2
          exact h2
        rw [Category.assoc, hsym, ← Category.assoc, hq]
        have hspec : ρo ≫ Work.DescentGeom.specGal σ
            = (Work.GCBasics.specOf (d.k') F).hom := by
          rw [hρ]
          rw [show Work.DescentGeom.specGal σ
              = Spec.map (CommRingCat.ofHom ((σ : (d.k') →+* (d.k')))) from rfl]
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rw [← hε]
          congr 1
        exact hspec)
    -- the same point, in the `Sch (D.k')`-form used by the comparison `B`
    let qσD : Work.GCBasics.FPt (Work.Charts.Sym (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g) F := qσ
    -- ## (F) the underlying closed point of `qσ ≫ AJSym` is `(galAct σ) x`.
    have hpt : (qσ ≫ d.exports.AJSym).left (IsLocalRing.closedPoint F)
        = (d.toChunk.galAct σ).hom x := by
      rw [Over.comp_left]
      show ((q.left ≫ (d.symGal σ).left) ≫ (d.exports.AJSym).left)
          (IsLocalRing.closedPoint F) = (d.toChunk.galAct σ).hom x
      rw [Category.assoc, ← Work.JacFinal.Inputs.AJSym_galAct_left d σ, ← Category.assoc,
        Scheme.Hom.comp_apply]
      exact congrArg _ hs
    -- ## (E) the class of `qσ ≫ AJSym` is `picAJ qσ`.
    have hcls : d.exports.glued.cls (qσ ≫ d.exports.AJSym) = d.chart.picAJ qσ :=
      Work.GroupChunk.Input.cls_AJSym d.chart qσ
    rw [← hpt]
    refine Work.JacClose.mem_chartRange_of_inChart_fpt d (qσ ≫ d.exports.AJSym)
      (hidx.symm ▸ i) ?_
    rw [hcls]
    -- ## (A) the comparison `β` identifies `B.pts qσ` and `B.pts q` (this is C5).
    have hβts : B.pts qσD = bq := by
      apply Over.OverMorphism.ext
      have hqσDleft : qσD.left = q.left ≫ (d.symGal σ).left := by
        dsimp only [qσD, qσ]
        rfl
      rw [B.pts_left, hbq, hqσDleft, Category.assoc]
      rw [show (d.symGal σ).left ≫ B.β = B.β from hsgb σ]
    -- ## (B) `B.pic0Map` of the two `picAJ`-classes agree: both are the class of
    -- `divOf (B.pts ·) - g·[P0]` on `C`, and `B.pts qσ = B.pts q`.
    have hB : B.pic0Map (d.chart.picAJ qσ) = c₀ := by
      rw [harr, hexp (F' := F) qσ]
      rw [show B.pts (F := F) qσ = bq from hβts]
    -- ## (C) the class statement transfers through `chartsK'` (TL′) and to `d.chart`.
    have hi' : Work.Charts.InChart D.d
        (Work.GCBasics.RPt.map εσD (D.E i)) (B.pic0Map (d.chart.picAJ qσ)) := by
      rw [hB]
      have hpt2 : Work.GCBasics.RPt.map εσD (D.E i)
          = Work.GCBasics.RPt.map εD (D.E (D.act σD i)) := by
        rw [show D.E (D.act σD i) = Work.GCBasics.RPt.map σD.toAlgHom (D.E i)
            from D.E_act σD i, Work.GCBasics.RPt.map_comp]
      rw [hpt2]
      exact hi σD
    have hTL := Work.Charts.GalCharts.inChart_of_inChart_k D
      (Work.SymQuot.instDivBase (C.baseChange D.k'))
      (Work.BNChart.rochDataPos (C.baseChange D.k') h')
      (Work.SymQuot.symGeomFamily (C.baseChange D.k')
        (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
      (Work.JacClose.posPt (C := C) (P0 := P0) h D) B (i := i)
      (c := d.chart.picAJ qσ) hi'
    have hInC : d.chart.InChart (hidx.symm ▸ i) (d.chart.picAJ qσ) := by
      obtain ⟨y, hy, hyc⟩ := hTL
      refine ⟨y, ?_, ?_⟩
      · rwa [show (D.chartsK' (Work.SymQuot.instDivBase (C.baseChange D.k'))
              (Work.BNChart.rochDataPos (C.baseChange D.k') h')
              (Work.SymQuot.symGeomFamily (C.baseChange D.k')
                (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
              (Work.JacClose.posPt (C := C) (P0 := P0) h D) B).d.V
            = d.chart.V from rfl] at hy
      · rw [← hyc]
        rw [show d.chart.picOf (hidx.symm ▸ i) y = Work.Charts.chartClass y
            (Work.GCBasics.RPt.map (IsScalarTower.toAlgHom D.k' D.k' F)
              ((D.chartsK' (Work.SymQuot.instDivBase (C.baseChange D.k'))
                (Work.BNChart.rochDataPos (C.baseChange D.k') h')
                (Work.SymQuot.symGeomFamily (C.baseChange D.k')
                  (Work.BNChart.rochDataPos (C.baseChange D.k') h').g)
                (Work.JacClose.posPt (C := C) (P0 := P0) h D) B).E i)) from rfl]
    exact hInC

  obtain ⟨s, hs⟩ := d.exports.AJSym_surjective x
  let F : Type u := Work.GCBasics.resField (d.chart.Sym d.chart.g) s
  letI : Field F := Work.GCBasics.resFieldField (d.chart.Sym d.chart.g) s
  let q : Work.GCBasics.FPt (d.chart.Sym d.chart.g) F :=
    Work.GCBasics.resPt (d.chart.Sym d.chart.g) s
  have hqcp : q.left (IsLocalRing.closedPoint F) = s := by
    dsimp only [q]
    exact Work.GCBasics.resPt_apply _ s _
  refine key F q ?_
  rw [hqcp]
  exact hs

end Work.JacClose

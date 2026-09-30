import Mathlib
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.pieceBdryHornIsoIso_inv
import Submission.Work.SSS.pieceBdryHornIso
import Submission.Work.SSS.pieceConnectingIso
import Submission.Work.SSS.sigmaVert_face
import Submission.Work.SSS.serreE1StepAux

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The peel step of `serreE1PieceIso` on an arbitrary relative cycle.**

Let `σ : Δ[P+1] ⟶ Sing B`, `z : C(T_σ)` of degree `(P+1)+t` a *relative* cycle (i.e. the projection
of `z` to `pieceAlong σ` is a cycle, `hzπ`), and `w' : C(T_{d_last σ})` of degree `P+t` whose
projection to `pieceAlong (d_lastσ)` is a cycle (`hw'π`), such that the class of `∂z` in
`C(T_σ)/C(Λ)` (Λ = `pieceHorn`) is `(-1)^(P+1)` times the class of `TIncl (lastFaceChain w')`
(`hpeel` — this is exactly the conclusion of `Work.SSS.iotaTBdryHorn` / `Work.SSS.hornCok_d_faceLift`
for `w'` the face-restriction of the lift of `z`).  Then the iterated last-face connecting map
`ε_σ = serreE1PieceIso p hfib (P+1) t σ` sends the class of the projection of `z` to `(-1)^(P+1)`
times (the base-point transport of) the value of `ε_{d_lastσ}` on the class of the projection of
`w'`.

This is the generic form of the induction step of `Work.SSS.serreE1PieceIso_iota`: the connecting
map is computed by `ShortComplex.ShortExact.δ_apply` for
`S := ShortComplex.SnakeInput.L₃ (kernelCokernelCompSequence.snakeInput (bdryIncl f σ) (TIncl f σ))`,
`hS := Work.SSS.cokernelComp_shortExact _ _`, with `x₃ := (pieceπOf σ) z`,
`x₂ := (hornCokπ σ) z`, and `x₁` any lift of `∂z` to `C(∂T_σ)` (which exists because
`x₃` is a cycle: `ker (pieceπOf) = range (sCCMap (bdryAlong).ι)`); then
`H(pieceBdryHornIsoIso)` is identified on `lastFaceChain`-classes by
`Work.SSS.pieceBdryHornIsoIso_inv` and the degree cast by `Work.SSS.sigmaVert_face`. -/
theorem pieceIso_peel (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (z : (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X ((P+1)+t))
    (hzπ : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d ((P+1)+t)
        ((ComplexShape.down ℕ).next ((P+1)+t))))
        ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f ((P+1)+t))) z) = 0)
    (w' : (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ))).X (P+t))
    (hw'π : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).d (P+t)
        ((ComplexShape.down ℕ).next (P+t))))
        ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).f (P+t))) w') = 0)
    (hpeel : (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((P+1)+t) ((P+1)+t-1))) z)
      = (-1 : ℤ)^(P+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f
                  ((P+1)+t-1)))
                (Work.SSS.castElem (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)))
                  (by omega : P+t = (P+1)+t-1) w')))) :
    (Work.SSS.serreE1PieceIso p hfib (P+1) t σ).hom
        ((HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) ((P+1)+t))
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f ((P+1)+t))) z)
            ((ComplexShape.down ℕ).next ((P+1)+t)) rfl hzπ))
      = (-1 : ℤ)^(P+1) •
          (CategoryTheory.eqToIso (congrArg (fun x : B => (Work.Cohomology.singularChains ℤ
              (TopCat.of (Work.StemsB.fibre p x))).homology t)
            (Work.SSS.sigmaVert_face (Fin.last (P+1)) (by
              intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv) σ))).hom
            ((Work.SSS.serreE1PieceIso p hfib P t
                (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).hom
              ((HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p)
                  (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)) (P+t))
                ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).cyclesMk
                  ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).f (P+t))) w')
                  ((ComplexShape.down ℕ).next (P+t)) rfl hw'π))) := by
  rw [← Work.SSS.serreE1PieceIso_succ_eq p hfib P t σ]
  simp only [Work.SSS.serreE1PieceStep, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  have h1deg : (P+1)+t-1 = P+t := by omega
  have h3deg : P+t = (P+1)+t-1 := by omega
  set yL : (Work.SSS.sCC (Work.SSS.bdryAlong (Work.SSS.sSingP p) σ)).X (P+t) :=
    (Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f (P+t) w' with hyL
  set w : (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ).X (P+t) :=
    (Work.SSS.bdryHornProj (Work.SSS.sSingP p) σ).f (P+t) yL with hw
  set u : (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
      ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).X (P+t) :=
    (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)
      ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f (P+t) yL) with hu
  set x1 : (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ).X ((P+1)+t-1) :=
    Work.SSS.castElem (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) h3deg
      ((-1 : ℤ)^(P+1) • w) with hx1def
  set x2 : (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
      ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).X ((P+1)+t) :=
    (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t) z with hx2def
  -- `snakeG` on `x2`
  have hx2 : (StepAux.snakeG (Work.SSS.sSingP p) P σ).f ((P+1)+t) x2
      = (Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f ((P+1)+t) z := by
    have h := congrArg (fun (g : Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ) ⟶
        cokernel (Work.SSS.TIncl (Work.SSS.sSingP p) σ)) => g.f ((P+1)+t))
      (StepAux.snakeG_π (Work.SSS.sSingP p) P σ)
    rw [HomologicalComplex.comp_f, Category.id_comp] at h
    have h2 := congrArg (fun (g : (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X ((P+1)+t)
        ⟶ (cokernel (Work.SSS.TIncl (Work.SSS.sSingP p) σ)).X ((P+1)+t)) =>
          (ConcreteCategory.hom g) z) h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [hx2def]
    exact h2
  -- `snakeF` on `w`
  have hSFn : (ConcreteCategory.hom ((StepAux.snakeF (Work.SSS.sSingP p) P σ).f (P+t))) w = u := by
    have h := congrArg (fun (g : Work.SSS.sCC (Work.SSS.bdryAlong (Work.SSS.sSingP p) σ) ⟶
        cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
          ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) => g.f (P+t))
      (StepAux.snakeF_π (Work.SSS.sSingP p) P σ)
    rw [HomologicalComplex.comp_f] at h
    have h2 := congrArg (fun (g : (Work.SSS.sCC (Work.SSS.bdryAlong (Work.SSS.sSingP p) σ)).X (P+t)
        ⟶ (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
          ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).X (P+t)) => (ConcreteCategory.hom g) yL) h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [hu]
    exact h2
  -- the differential of the horn quotient on `x2`
  have hD : (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
        ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).d ((P+1)+t) ((P+1)+t-1) x2
      = (-1 : ℤ)^(P+1) • Work.SSS.castElem (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
          ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) h3deg u := by
    have hcomm := congrArg (fun (g : (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X ((P+1)+t)
        ⟶ (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
          ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).X ((P+1)+t-1)) => g z)
      (HomologicalComplex.Hom.comm (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ)
        ((P+1)+t) ((P+1)+t-1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
    rw [hx2def, hcomm, hpeel]
    rw [← StepAux.castElem_map (Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ) h3deg w']
    rw [← hyL]
    rw [← StepAux.castElem_map (Work.SSS.TIncl (Work.SSS.sSingP p) σ) h3deg yL]
    rw [← StepAux.castElem_map (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ) h3deg
      ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f (P+t) yL)]
  -- `snakeF` on `x1`
  have hx1 : (StepAux.snakeF (Work.SSS.sSingP p) P σ).f ((P+1)+t-1) x1
      = (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
          ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).d ((P+1)+t) ((P+1)+t-1) x2 := by
    have hzmF : (ConcreteCategory.hom ((StepAux.snakeF (Work.SSS.sSingP p) P σ).f (P+t)))
          ((-1 : ℤ)^(P+1) • w)
        = (-1 : ℤ)^(P+1) • (ConcreteCategory.hom
            ((StepAux.snakeF (Work.SSS.sSingP p) P σ).f (P+t))) w :=
      map_zsmul _ _ _
    have hcm := StepAux.castElem_map (K := Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ)
      (StepAux.snakeF (Work.SSS.sSingP p) P σ) h3deg ((-1 : ℤ)^(P+1) • w)
    rw [hx1def]
    refine hcm.symm.trans ?_
    refine (congrArg (Work.SSS.castElem (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
      ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) h3deg) hzmF).trans ?_
    rw [StepAux.castElem_zsmul, hSFn, hD]
  -- `x1` is a cycle
  have hx1c : (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ).d ((P+1)+t-1)
      ((ComplexShape.down ℕ).next ((P+1)+t-1)) x1 = 0 := by
    haveI : Mono (Work.SSS.TIncl (Work.SSS.sSingP p) σ) := StepAux.mono_TIncl _ _
    have hS : (ShortComplex.SnakeInput.L₃ (kernelCokernelCompSequence.snakeInput
        (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ)
        (Work.SSS.TIncl (Work.SSS.sSingP p) σ))).ShortExact :=
      Work.SSS.cokernelComp_shortExact _ _
    have hij : (ComplexShape.down ℕ).Rel ((P+1)+t) ((P+1)+t-1) :=
      ComplexShape.down_mk (j := (P+1)+t) (i := (P+1)+t-1) (by omega)
    exact ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply hS ((P+1)+t) ((P+1)+t-1)
      x2 x1 hx1 ((ComplexShape.down ℕ).next ((P+1)+t-1))
  -- the connecting map on the class
  have hA : (ModuleCat.Hom.hom ((Work.SSS.pieceConnectingIsoIso (Work.SSS.sSingP p) P σ ((P+1)+t)
        (by omega) (Work.SSS.pieceHornC_acyclic_succ p hfib P σ ((P+1)+t))
        (Work.SSS.pieceHornC_acyclic_succ p hfib P σ ((P+1)+t-1))).hom))
      ((ConcreteCategory.hom (HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) ((P+1)+t)))
        (HomologicalComplex.cyclesMk (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ)
          ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f ((P+1)+t))) z)
          ((ComplexShape.down ℕ).next ((P+1)+t)) rfl hzπ))
      = (ConcreteCategory.hom (HomologicalComplex.homologyπ
          (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) ((P+1)+t-1)))
          (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) x1
            ((ComplexShape.down ℕ).next ((P+1)+t-1)) rfl hx1c) :=
    StepAux.eA_apply (Work.SSS.sSingP p) P ((P+1)+t) (by omega) σ
      (Work.SSS.pieceHornC_acyclic_succ p hfib P σ ((P+1)+t))
      (Work.SSS.pieceHornC_acyclic_succ p hfib P σ ((P+1)+t-1))
      ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f ((P+1)+t))) z) hzπ
      x2 hx2 x1 hx1 hx1c
  -- the cast of `x1`
  have hcast : Work.SSS.castElem (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) h1deg x1
      = (-1 : ℤ)^(P+1) • w := by
    rw [hx1def, StepAux.castElem_trans, StepAux.castElem_zsmul,
      StepAux.castElem_irrel (h3deg.trans h1deg) rfl w]
    simp [Work.SSS.castElem]
  -- the last-face isomorphism on `w`
  have hw' : (ConcreteCategory.hom ((Work.SSS.pieceBdryHornIsoIso (Work.SSS.sSingP p) P σ).hom.f (P+t))) w
      = (ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).f (P+t))) w' := by
    rw [hw, hyL]
    exact StepAux.pieceBdryHornIsoIso_hom_apply (Work.SSS.sSingP p) P (P+t) σ w'
  -- the cycle comparison
  have hcyc_eq : HomologicalComplex.cyclesMap (Work.SSS.pieceBdryHornIsoIso (Work.SSS.sSingP p) P σ).hom
        (P+t)
        (StepAux.castCycles (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) h1deg
          (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) x1
            ((ComplexShape.down ℕ).next ((P+1)+t-1)) rfl hx1c))
      = (-1 : ℤ)^(P+1) • HomologicalComplex.cyclesMk
          (Work.SSS.pieceAlong (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ))
          ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).f (P+t))) w')
          ((ComplexShape.down ℕ).next (P+t)) rfl hw'π := by
    apply (Preadditive.mono_iff_injective ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).iCycles (P+t))).1 inferInstance
    simp only [StepAux.forget2_Ab_hom_apply]
    rw [map_zsmul, StepAux.iCycles_cyclesMk]
    have hci := congrArg (fun (g : (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ).cycles (P+t) ⟶
        (Work.SSS.pieceAlong (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).X (P+t)) =>
          g (StepAux.castCycles (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) h1deg
            (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) x1
              ((ComplexShape.down ℕ).next ((P+1)+t-1)) rfl hx1c)))
      (HomologicalComplex.cyclesMap_i
        (φ := (Work.SSS.pieceBdryHornIsoIso (Work.SSS.sSingP p) P σ).hom) (i := P+t))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hci
    rw [StepAux.iCycles_castCycles, StepAux.iCycles_cyclesMk] at hci
    rw [hcast] at hci
    rw [map_zsmul, hw'] at hci
    exact hci
  -- the degree cast and the last-face isomorphism on the homology class
  have hcore : (ModuleCat.Hom.hom ((HomologicalComplex.homologyMapIso
        (Work.SSS.pieceBdryHornIsoIso (Work.SSS.sSingP p) P σ) (P+t)).hom))
      ((ModuleCat.Hom.hom ((eqToIso (congrArg (fun m =>
          (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ).homology m) h1deg)).hom))
        ((ConcreteCategory.hom (HomologicalComplex.homologyπ
            (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) ((P+1)+t-1)))
          (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) x1
            ((ComplexShape.down ℕ).next ((P+1)+t-1)) rfl hx1c)))
      = (-1 : ℤ)^(P+1) •
          (ConcreteCategory.hom (HomologicalComplex.homologyπ
            (Work.SSS.pieceAlong (Work.SSS.sSingP p)
              (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)) (P+t)))
          (HomologicalComplex.cyclesMk (Work.SSS.pieceAlong (Work.SSS.sSingP p)
              (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ))
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
              (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).f (P+t))) w')
            ((ComplexShape.down ℕ).next (P+t)) rfl hw'π) := by
    rw [StepAux.eqToIso_homologyπ (K := Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) h1deg
      (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ) x1
        ((ComplexShape.down ℕ).next ((P+1)+t-1)) rfl hx1c)]
    rw [show (ModuleCat.Hom.hom ((HomologicalComplex.homologyMapIso
          (Work.SSS.pieceBdryHornIsoIso (Work.SSS.sSingP p) P σ) (P+t)).hom))
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.SSS.pieceBdryHornIsoIso (Work.SSS.sSingP p) P σ).hom (P+t))) from rfl]
    rw [StepAux.homologyMap_homologyπ]
    rw [hcyc_eq, map_zsmul]
  rw [hA, hcore, map_zsmul, map_zsmul]


end Work.SSS

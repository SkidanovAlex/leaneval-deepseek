import Mathlib
import Submission.Work.SSS.serreE1CruxD1
import Submission.Work.SSS.d_sndToR_iotaTLin
import Submission.Work.SSS.iotaT_eq_iotaTLin
import Submission.Work.SSS.homologyMap_cyclesMk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- For an isomorphism `e : M ≅ N` of `ℤ`-modules, `e.inv ∘ e.hom = id` on elements. -/
private lemma kFpg_iso_inv_hom_apply {M N : ModuleCat ℤ} (e : M ≅ N) (y : M) :
    ModuleCat.Hom.hom e.inv (ModuleCat.Hom.hom e.hom y) = y := by
  have h := Iso.hom_inv_id e
  have h2 := congrArg (fun (f : M ⟶ M) => ModuleCat.Hom.hom f y) h
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h2

/-- **`mapPhiY` on the σ-piece generator `ι_σ z`.**  The `σ`-summand inclusion `mapPhiY` of the
graded piece, evaluated on the piece class of `ι_σ z`, is the `grFι`-image of the second projection
of the lifted Eilenberg–Zilber chain `iotaTLin` into the filtration term `R_{s+1}`.

Route: `iotaF = iotaT ≫ pieceπOf`, `pieceπOf = pieceπ` definitionally, and
`Work.SSS.thetaPhi_mapPhiY_apply_f` computes `pieceπ ≫ mapPhiY = sCCMap (sndToR) ≫ grFι` on
elements; finally `Work.SSS.iotaT_eq_iotaTLin` identifies `iotaT z` with `iotaTLin z`. -/
private lemma kFpg_mapPhiY_iotaF (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1))
    (z : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).X t) :
    (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
      ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)
    = (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
        (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)) := by
  have hkey : (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.pieceπ (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
        ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
          (s+1) (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z))
      = (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
          ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
            (s+1) (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)) :=
    congrArg (fun (g : (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
        (Work.SSS.sigHat σ))).X ((s+1)+t) ⟶
        (Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).X ((s+1)+t)) =>
      (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) (s+1) (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
        (Work.SSS.sigHat σ) rfl t)) z))
    (Work.SSS.thetaPhi_mapPhiY_apply_f (Work.SSS.sSingP p) (s+1) ((s+1)+t) σ)
  have h1 : (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
      ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)
      = (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.pieceπ (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
          ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
            (s+1) (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)) := rfl
  have h2 : (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
          (s+1) (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z))
      = (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)) :=
    congrArg (fun w => (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t))) w))
      (Work.SSS.iotaT_eq_iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)
  exact Eq.trans (Eq.trans h1 hkey) h2

/-- **The connecting map `kF` on the generators of the first page.**  For the canonical Serre
filtration `xiCan p`, the composite `Work.SSS.PsiCoef σ ≫ H(mapPhiY σ) ≫ kF` sends the class
`(triv_b) (homologyπ z)` of the cycle `z` to `c (s+1)` times the class of the alternating face sum
`faceSum`.

Route: `(PsiCoef σ).hom = triv.inv ≫ (serreE1PieceIso σ).inv`; the inverse form of the sign spec
(`Work.SSS.PieceInv` from `hal` and `hc1` via `Work.SSS.pieceInv_of_pieceAlpha`) computes
`(serreE1PieceIso σ).inv (homologyπ z) = c (s+1) • [ι_σ z]`; then
`Work.SSS.mapPhiY_iotaF_gen` rewrites `H(mapPhiY σ) [ι_σ z]` as
`[grFι f (s+1) ((sCCMap (sndToR σ)) (iotaTLin σ z))]` (via
`Work.SSS.homologyMap_cyclesMk` and `Work.SSS.IotaChain.iotaF_cycle`); then
`Work.SSS.kF_eq_of_lift` with `w := (sCCMap (sndToR σ)) (iotaTLin σ z))` (whose
`cokernel.π`-image is the `grFι`-image by `Work.SSS.grFι_succ`), `v := faceSum` and
`hv := Work.SSS.d_sndToR_iotaTLin` produces the class of `faceSum`; the cycle condition `hvcyc`
is a hypothesis. -/
theorem kF_psiCoef_gen (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSS.PieceAlpha p hfib c) :
    ∀ (s : ℕ) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1))
      (z : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).X t)
      (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p
          (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).d t
          ((ComplexShape.down ℕ).next t))) z = 0)
      (hvcyc : (ModuleCat.Hom.hom (((Work.SSS.Fc p).obj s).d (s+t)
          ((ComplexShape.down ℕ).next (s+t))))
        (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z) = 0),
      (ModuleCat.Hom.hom ((Work.SSS.PsiCoef p e₀ hfib hc t (s+1) σ).hom ≫
          HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t) ≫
          Work.SSS.kF (Work.SSS.xiCan p) s t))
        ((Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
          ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
            ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
              ((ComplexShape.down ℕ).next t) rfl hz)))
        = c (s+1) • ((Work.SSS.Fc p).obj s).homologyπ (s+t)
            (((Work.SSS.Fc p).obj s).cyclesMk
              (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
                (Work.SSS.sigHat σ) rfl z)
              ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc) := by
  intro s σ z hz hvcyc
  have hy := Work.SSS.IotaChain.iotaF_cycle p hfib (s+1) t
      (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z hz
  have hpinv := Work.SSS.pieceInv_of_pieceAlpha p hfib c hc1 hal (s+1) t
      (Work.SSS.sigHat σ) z hz hy
  have htriv := kFpg_iso_inv_hom_apply (Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)))
    ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
      ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
        ((ComplexShape.down ℕ).next t) rfl hz))
  have hx' : (ModuleCat.Hom.hom ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).d ((s+1)+t)
        ((ComplexShape.down ℕ).next ((s+1)+t))))
      ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
        ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
          (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)) = 0 := by
    refine Eq.trans (Work.SSS.chainMap_comm_apply_elem (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ)
      (i := (s+1)+t) (j := (ComplexShape.down ℕ).next ((s+1)+t))
      ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)) ?_
    exact Eq.trans (congrArg (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f
      ((ComplexShape.down ℕ).next ((s+1)+t)))) hy) (map_zero _)
  have hmapPhiY := kFpg_mapPhiY_iotaF p hfib s t σ z
  have hz' : (ModuleCat.Hom.hom ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).d ((s+1)+t)
        ((ComplexShape.down ℕ).next ((s+1)+t))))
      ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z))) = 0 := by
    rw [← hmapPhiY]
    exact hx'
  have hz'' : (ModuleCat.Hom.hom ((Work.SSS.grF (Work.SSS.xiCan p).F (s+1)).d ((s+1)+t)
        ((ComplexShape.down ℕ).next ((s+1)+t))))
      ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z))) = 0 :=
    hz'
  have hv : (ModuleCat.Hom.hom ((Work.SSS.incF (Work.SSS.Fc p) s).f (s+t)))
        (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)
      = (ModuleCat.Hom.hom (((Work.SSS.Fc p).obj (s+1)).d ((s+1)+t) (s+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)) :=
    (Work.SSS.d_sndToR_iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) σ rfl z hz).symm
  have hv' : (ModuleCat.Hom.hom ((Work.SSS.incF (Work.SSS.xiCan p).F s).f (s+t)))
        (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)
      = (ModuleCat.Hom.hom (((Work.SSS.xiCan p).F.obj (s+1)).d ((s+1)+t) (s+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)) :=
    hv
  have hvcyc' : (ModuleCat.Hom.hom (((Work.SSS.xiCan p).F.obj s).d (s+t)
        ((ComplexShape.down ℕ).next (s+t))))
      (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
        (Work.SSS.sigHat σ) rfl z) = 0 := hvcyc
  have hkf := Work.SSS.kF_eq_of_lift (Work.SSS.xiCan p) s t
    ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
        (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)))
    hz''
    ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
      (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z))
    rfl
    (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)
    hv' hvcyc'
  have hhm : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t)))
      ((Work.SSS.pieceAlong (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).homologyπ ((s+1)+t)
        ((Work.SSS.pieceAlong (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).cyclesMk
          ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
            (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy))
      = (Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).homologyπ ((s+1)+t)
        ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
              (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx') :=
    (Work.SSS.homologyMap_cyclesMk (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ)
      (hj := rfl)
      ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z) hy hx').symm
  have hbridge : (Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).homologyπ ((s+1)+t)
        ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
              (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx')
      = (Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).homologyπ ((s+1)+t)
        ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
              (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz') := by
    have hcycEq : (Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
              (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx'
        = (Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
              (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz' := by
      apply (Preadditive.mono_iff_injective
        ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).iCycles ((s+1)+t))).1 inferInstance
      show (ConcreteCategory.hom
            ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).iCycles ((s+1)+t)))
          ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
              ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
                (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z))
            ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx')
        = (ConcreteCategory.hom
            ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).iCycles ((s+1)+t)))
          ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
                (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)))
            ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz')
      exact (Work.SSS.hmcm_iCycles_cyclesMk (i := (s+1)+t)
            (j := (ComplexShape.down ℕ).next ((s+1)+t)) rfl
            ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
              ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
                (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)) hx').trans
        (hmapPhiY.trans (Work.SSS.hmcm_iCycles_cyclesMk (i := (s+1)+t)
            (j := (ComplexShape.down ℕ).next ((s+1)+t)) rfl
            ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
                (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z))) hz').symm)
    exact congrArg (fun w => (Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).homologyπ
      ((s+1)+t) w) hcycEq
  calc
    (ModuleCat.Hom.hom ((Work.SSS.PsiCoef p e₀ hfib hc t (s+1) σ).hom ≫
        HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t) ≫
        Work.SSS.kF (Work.SSS.xiCan p) s t))
      ((Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
        ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
          ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz)))
      = (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSS.PsiCoef p e₀ hfib hc t (s+1) σ).hom)
              ((ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom)
                ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
                  ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
                    ((ComplexShape.down ℕ).next t) rfl hz))))) := rfl
    _ = (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSS.serreE1PieceIso p hfib (s+1) t (Work.SSS.sigHat σ)).inv)
              ((ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).inv)
                ((ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom)
                  ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
                    ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
                      ((ComplexShape.down ℕ).next t) rfl hz)))))) := rfl
    _ = (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSS.serreE1PieceIso p hfib (s+1) t (Work.SSS.sigHat σ)).inv)
              ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
                ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
                  ((ComplexShape.down ℕ).next t) rfl hz)))) := by
          refine congrArg (fun w => (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t)))
              ((ModuleCat.Hom.hom (Work.SSS.serreE1PieceIso p hfib (s+1) t (Work.SSS.sigHat σ)).inv) w))) ?_
          exact htriv
    _ = (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t)))
            (c (s+1) • ((Work.SSS.pieceAlong (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).homologyπ ((s+1)+t)
              ((Work.SSS.pieceAlong (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).cyclesMk
                ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
                  (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)
                ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy)))) := by
          exact congrArg (fun w => (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t))) w)) hpinv
    _ = c (s+1) • (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t)))
            ((Work.SSS.pieceAlong (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).homologyπ ((s+1)+t)
              ((Work.SSS.pieceAlong (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).cyclesMk
                ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
                  (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)
                ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy))) := by
          exact (congrArg (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
            (map_zsmul (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
                (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ) ((s+1)+t))) (c (s+1))
              ((Work.SSS.pieceAlong (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).homologyπ ((s+1)+t)
                ((Work.SSS.pieceAlong (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).cyclesMk
                  ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
                    (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z)
                  ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy)))).trans
            (map_zsmul (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t)) (c (s+1)) _)
    _ = c (s+1) • (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
          ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).homologyπ ((s+1)+t)
            ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
              ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)))
                ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1)
                  (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl t)) z))
              ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx')) := by
          exact congrArg (fun w => c (s+1) • (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t)) w) hhm
    _ = c (s+1) • (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t))
          ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).homologyπ ((s+1)+t)
            ((Work.SSS.grF (Work.SSS.serF (Work.SSS.sSingP p)) (s+1)).cyclesMk
              ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t)))
                ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
                  (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)))
              ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz')) := by
          exact congrArg (fun w => c (s+1) • (ModuleCat.Hom.hom (Work.SSS.kF (Work.SSS.xiCan p) s t)) w) hbridge
    _ = c (s+1) • ((Work.SSS.xiCan p).F.obj s).homologyπ (s+t)
          (((Work.SSS.xiCan p).F.obj s).cyclesMk
            (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
              (Work.SSS.sigHat σ) rfl z)
            ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc) := by
          exact congrArg (fun (w : ((Work.SSS.xiCan p).F.obj s).homology (s+t)) => c (s+1) • w) hkf

end Work.SSS

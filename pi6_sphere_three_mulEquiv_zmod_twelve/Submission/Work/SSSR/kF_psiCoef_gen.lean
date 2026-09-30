import Mathlib
import Submission.Work.SSSR.serreE1CruxD1
import Submission.Work.SSSR.d_sndToR_iotaTLin
import Submission.Work.SSSR.iotaT_eq_iotaTLin
import Submission.Work.SSSR.homologyMap_cyclesMk
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- For an isomorphism `e : M ≅ N` of `ℤ`-modules, `e.inv ∘ e.hom = id` on elements. -/
private lemma kFpg_iso_inv_hom_apply {M N : ModuleCat R} (e : M ≅ N) (y : M) :
    ModuleCat.Hom.hom e.inv (ModuleCat.Hom.hom e.hom y) = y := by
  have h := Iso.hom_inv_id e
  have h2 := congrArg (fun (f : M ⟶ M) => ModuleCat.Hom.hom f y) h
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h2

/-- **`mapPhiY R` on the σ-piece generator `ι_σ z`.**  The `σ`-summand inclusion `mapPhiY R` of the
graded piece, evaluated on the piece class of `ι_σ z`, is the `grFι R`-image of the second projection
of the lifted Eilenberg–Zilber chain `iotaTLin` into the filtration term `R_{s+1}`.

Route: `iotaF = iotaT ≫ pieceπOf`, `pieceπOf = pieceπ R` definitionally, and
`Work.SSSR.thetaPhi_mapPhiY_apply_f` computes `pieceπ R ≫ mapPhiY R = sCCMap R (sndToR) ≫ grFι R` on
elements; finally `Work.SSSR.iotaT_eq_iotaTLin` identifies `iotaT z` with `iotaTLin z`. -/
private lemma kFpg_mapPhiY_iotaF (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s t : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1))
    (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X t) :
    (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
      ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)
    = (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
        (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)) := by
  have hkey : (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
        ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
          (s+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z))
      = (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
            (s+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)) :=
    congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (Work.SSSR.sigHat σ))).X ((s+1)+t) ⟶
        (Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).X ((s+1)+t)) =>
      (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (s+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (Work.SSSR.sigHat σ) rfl t)) z))
    (Work.SSSR.thetaPhi_mapPhiY_apply_f (Work.SSSR.sSingP p) (s+1) ((s+1)+t) σ)
  have h1 : (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
      ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)
      = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
            (s+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)) := rfl
  have h2 : (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
          (s+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z))
      = (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)) :=
    congrArg (fun w => (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t))) w))
      (Work.SSSR.iotaT_eq_iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)
  exact Eq.trans (Eq.trans h1 hkey) h2

/-- **The connecting map `kF` on the generators of the first page.**  For the canonical Serre
filtration `xiCan p`, the composite `Work.SSSR.PsiCoef σ ≫ H(mapPhiY R σ) ≫ kF` sends the class
`(triv_b) (homologyπ z)` of the cycle `z` to `c (s+1)` times the class of the alternating face sum
`faceSum`.

Route: `(PsiCoef σ).hom = triv.inv ≫ (serreE1PieceIso σ).inv`; the inverse form of the sign spec
(`Work.SSSR.PieceInv` from `hal` and `hc1` via `Work.SSSR.pieceInv_of_pieceAlpha`) computes
`(serreE1PieceIso σ).inv (homologyπ z) = c (s+1) • [ι_σ z]`; then
`Work.SSSR.mapPhiY_iotaF_gen` rewrites `H(mapPhiY R σ) [ι_σ z]` as
`[grFι R f (s+1) ((sCCMap R (sndToR σ)) (iotaTLin σ z))]` (via
`Work.SSSR.homologyMap_cyclesMk` and `Work.SSSR.IotaChain.iotaF_cycle`); then
`Work.SSSR.kF_eq_of_lift` with `w := (sCCMap R (sndToR σ)) (iotaTLin σ z))` (whose
`cokernel.π`-image is the `grFι R`-image by `Work.SSSR.grFι_succ`), `v := faceSum` and
`hv := Work.SSSR.d_sndToR_iotaTLin` produces the class of `faceSum`; the cycle condition `hvcyc`
is a hypothesis. -/
theorem kF_psiCoef_gen (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSSR.PieceAlpha (R := R) p hfib c) :
    ∀ (s : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1))
      (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X t)
      (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).d t
          ((ComplexShape.down ℕ).next t))) z = 0)
      (hvcyc : (ModuleCat.Hom.hom (((Work.SSSR.Fc p).obj s).d (s+t)
          ((ComplexShape.down ℕ).next (s+t))))
        (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z) = 0),
      (ModuleCat.Hom.hom ((Work.SSSR.PsiCoef p e₀ hfib hc t (s+1) σ).hom ≫
          HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t) ≫
          Work.SSSR.kF (Work.SSSR.xiCan p) s t))
        ((Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
          ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
            ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
              ((ComplexShape.down ℕ).next t) rfl hz)))
        = c (s+1) • ((Work.SSSR.Fc p).obj s).homologyπ (s+t)
            (((Work.SSSR.Fc p).obj s).cyclesMk
              (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
                (Work.SSSR.sigHat σ) rfl z)
              ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc) := by
  intro s σ z hz hvcyc
  have hy := Work.SSSR.IotaChain.iotaF_cycle p hfib (s+1) t
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z hz
  have hpinv := Work.SSSR.pieceInv_of_pieceAlpha p hfib c hc1 hal (s+1) t
      (Work.SSSR.sigHat σ) z hz hy
  have htriv := kFpg_iso_inv_hom_apply (Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)))
    ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
      ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
        ((ComplexShape.down ℕ).next t) rfl hz))
  have hx' : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).d ((s+1)+t)
        ((ComplexShape.down ℕ).next ((s+1)+t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
        ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)) = 0 := by
    refine Eq.trans (Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ)
      (i := (s+1)+t) (j := (ComplexShape.down ℕ).next ((s+1)+t))
      ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)) ?_
    exact Eq.trans (congrArg (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f
      ((ComplexShape.down ℕ).next ((s+1)+t)))) hy) (map_zero _)
  have hmapPhiY := kFpg_mapPhiY_iotaF p hfib s t σ z
  have hz' : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).d ((s+1)+t)
        ((ComplexShape.down ℕ).next ((s+1)+t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z))) = 0 := by
    rw [← hmapPhiY]
    exact hx'
  have hz'' : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.xiCan p).F (s+1)).d ((s+1)+t)
        ((ComplexShape.down ℕ).next ((s+1)+t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z))) = 0 :=
    hz'
  have hv : (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.Fc p) s).f (s+t)))
        (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)
      = (ModuleCat.Hom.hom (((Work.SSSR.Fc p).obj (s+1)).d ((s+1)+t) (s+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)) :=
    (Work.SSSR.d_sndToR_iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) σ rfl z hz).symm
  have hv' : (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.xiCan p).F s).f (s+t)))
        (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)
      = (ModuleCat.Hom.hom (((Work.SSSR.xiCan p).F.obj (s+1)).d ((s+1)+t) (s+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
          (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)) :=
    hv
  have hvcyc' : (ModuleCat.Hom.hom (((Work.SSSR.xiCan p).F.obj s).d (s+t)
        ((ComplexShape.down ℕ).next (s+t))))
      (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (Work.SSSR.sigHat σ) rfl z) = 0 := hvcyc
  have hkf := Work.SSSR.kF_eq_of_lift (Work.SSSR.xiCan p) s t
    ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
        (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)))
    hz''
    ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
      (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z))
    rfl
    (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)
    hv' hvcyc'
  have hhm : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t)))
      ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).homologyπ ((s+1)+t)
        ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).cyclesMk
          ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy))
      = (Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).homologyπ ((s+1)+t)
        ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx') :=
    (Work.SSSR.homologyMap_cyclesMk (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ)
      (hj := rfl)
      ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z) hy hx').symm
  have hbridge : (Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).homologyπ ((s+1)+t)
        ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx')
      = (Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).homologyπ ((s+1)+t)
        ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
              (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz') := by
    have hcycEq : (Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx'
        = (Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
              (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)))
          ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz' := by
      apply (Preadditive.mono_iff_injective
        ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).iCycles ((s+1)+t))).1 inferInstance
      show (ConcreteCategory.hom
            ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).iCycles ((s+1)+t)))
          ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
              ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z))
            ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx')
        = (ConcreteCategory.hom
            ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).iCycles ((s+1)+t)))
          ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
                (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)))
            ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz')
      exact (Work.SSSR.hmcm_iCycles_cyclesMk (i := (s+1)+t)
            (j := (ComplexShape.down ℕ).next ((s+1)+t)) rfl
            ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
              ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)) hx').trans
        (hmapPhiY.trans (Work.SSSR.hmcm_iCycles_cyclesMk (i := (s+1)+t)
            (j := (ComplexShape.down ℕ).next ((s+1)+t)) rfl
            ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
                (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z))) hz').symm)
    exact congrArg (fun w => (Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).homologyπ
      ((s+1)+t) w) hcycEq
  calc
    (ModuleCat.Hom.hom ((Work.SSSR.PsiCoef p e₀ hfib hc t (s+1) σ).hom ≫
        HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t) ≫
        Work.SSSR.kF (Work.SSSR.xiCan p) s t))
      ((Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
        ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
          ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz)))
      = (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSSR.PsiCoef p e₀ hfib hc t (s+1) σ).hom)
              ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom)
                ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
                  ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
                    ((ComplexShape.down ℕ).next t) rfl hz))))) := rfl
    _ = (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSSR.serreE1PieceIso p hfib (s+1) t (Work.SSSR.sigHat σ)).inv)
              ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).inv)
                ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom)
                  ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
                    ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
                      ((ComplexShape.down ℕ).next t) rfl hz)))))) := rfl
    _ = (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t)))
            ((ModuleCat.Hom.hom (Work.SSSR.serreE1PieceIso p hfib (s+1) t (Work.SSSR.sigHat σ)).inv)
              ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
                ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
                  ((ComplexShape.down ℕ).next t) rfl hz)))) := by
          refine congrArg (fun w => (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t)))
              ((ModuleCat.Hom.hom (Work.SSSR.serreE1PieceIso p hfib (s+1) t (Work.SSSR.sigHat σ)).inv) w))) ?_
          exact htriv
    _ = (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t)))
            (c (s+1) • ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).homologyπ ((s+1)+t)
              ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).cyclesMk
                ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)
                ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy)))) := by
          exact congrArg (fun w => (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t))) w)) hpinv
    _ = c (s+1) • (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t)))
            ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).homologyπ ((s+1)+t)
              ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).cyclesMk
                ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)
                ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy))) := by
          exact (congrArg (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
            (map_zsmul (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
                (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ) ((s+1)+t))) (c (s+1))
              ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).homologyπ ((s+1)+t)
                ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).cyclesMk
                  ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
                    (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z)
                  ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy)))).trans
            (map_zsmul (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t)) (c (s+1)) _)
    _ = c (s+1) • (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
          ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).homologyπ ((s+1)+t)
            ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
              ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) (s+1) σ).f ((s+1)+t)))
                ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1)
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl t)) z))
              ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hx')) := by
          exact congrArg (fun w => c (s+1) • (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t)) w) hhm
    _ = c (s+1) • (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t))
          ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).homologyπ ((s+1)+t)
            ((Work.SSSR.grF (Work.SSSR.serF R (Work.SSSR.sSingP p)) (s+1)).cyclesMk
              ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (s+1)).f ((s+1)+t)))
                ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
                  (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)))
              ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz')) := by
          exact congrArg (fun w => c (s+1) • (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) s t)) w) hbridge
    _ = c (s+1) • ((Work.SSSR.xiCan p).F.obj s).homologyπ (s+t)
          (((Work.SSSR.xiCan p).F.obj s).cyclesMk
            (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
              (Work.SSSR.sigHat σ) rfl z)
            ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc) := by
          exact congrArg (fun (w : ((Work.SSSR.xiCan p).F.obj s).homology (s+t)) => c (s+1) • w) hkf

end Work.SSSR

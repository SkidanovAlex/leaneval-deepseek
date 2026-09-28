import Mathlib
import Submission.Work.SSS.chainCondAux
import Submission.Work.SSS.faceRestr_eq_ezSimplex

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `cyclesMk` only depends on the underlying element of the complex. -/
lemma fcn_cyclesMk_congr {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ} {x x' : K.X i} (hxx : x = x')
    (hx : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x = 0)
    (hx' : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x' = 0) :
    K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx
      = K.cyclesMk x' ((ComplexShape.down ℕ).next i) rfl hx' := by
  apply (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance
  show (ConcreteCategory.hom (K.iCycles i))
      (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)
    = (ConcreteCategory.hom (K.iCycles i))
      (K.cyclesMk x' ((ComplexShape.down ℕ).next i) rfl hx')
  rw [show (ConcreteCategory.hom (K.iCycles i))
        (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx) = x from by
      simpa using HomologicalComplex.i_cyclesMk (K := K) x ((ComplexShape.down ℕ).next i) rfl hx,
    show (ConcreteCategory.hom (K.iCycles i))
        (K.cyclesMk x' ((ComplexShape.down ℕ).next i) rfl hx') = x' from by
      simpa using HomologicalComplex.i_cyclesMk (K := K) x' ((ComplexShape.down ℕ).next i) rfl hx',
    hxx]

/-- `homologyπ` of a cycle class only depends on the underlying element. -/
lemma fcn_homologyπ_cyclesMk_congr {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ} {x x' : K.X i}
    (hxx : x = x')
    (hx : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x = 0)
    (hx' : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x' = 0) :
    K.homologyπ i (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)
      = K.homologyπ i (K.cyclesMk x' ((ComplexShape.down ℕ).next i) rfl hx') := by
  rw [fcn_cyclesMk_congr hxx hx hx']

/-- For a nondegenerate face `i ≠ 0` of a nondegenerate `(s+1)`-simplex `σ`, the class of
`(grFι s)(faceB i)` in `H_{s+t}(grF_s)` is `c s` times the `H(mapPhiY ρ_i)`-image of
`(PsiCoef ρ_i).hom` of the trivialised class of `z`. -/
theorem faceB_class_nondeg (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSS.PieceAlpha p hfib c)
    (s : ℕ) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1))
    (z : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (i : Fin (s+2)) (hi : i ≠ 0)
    (hnd : SimplicialObject.δ (Work.SSS.sSing B) i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ)
      ∈ (Work.SSS.sSing B).nonDegenerate s) :
    (Work.SSS.grF (Work.SSS.Fc p) s).homologyπ (s+t)
      ((Work.SSS.grF (Work.SSS.Fc p) s).cyclesMk
        ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t))
          (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
            (Work.SSS.sigHat σ) rfl z i)))
        ((ComplexShape.down ℕ).next (s+t)) rfl
        (Work.SSS.grFι_faceB_cycle p hfib s t σ z hz i))
      = c s • (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
            (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
              ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩)) (s+t))
          ((Work.SSS.PsiCoef p e₀ hfib hc t s
            (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
              ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩)).hom
            ((Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
              ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
                ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
                  ((ComplexShape.down ℕ).next t) rfl hz)))) := by
  set ρ : Work.SSS.nIndex (Work.SSS.sSing B) s :=
    Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
      ⟨SimplicialObject.δ (Work.SSS.sSing B) i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩
    with hρdef
  have hρi : SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ =
      Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ := by
    rw [hρdef]
    have h := Work.SSS.nIndexSigma_face σ i hnd
    rw [h]
    congr 1
  have h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ)
      = Work.SSS.sigmaVert (Work.SSS.sigHat σ) :=
    Work.SSS.sigmaVert_face i hi (Work.SSS.sigHat σ)
  have h'' : Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ)
      = Work.SSS.sigmaVert (Work.SSS.sigHat σ) :=
    (congrArg Work.SSS.sigmaVert hρi).symm.trans h'
  let X : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ)).X (s+t) :=
    (ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
      (Work.SSS.liftFam_proj p hfib) s (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ) h'' t)) z
  have hkey : (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t)))
        (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z i)
      = (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ).f (s+t))) X := by
    rw [Work.SSS.faceB_grFi_nondeg p hfib s t σ (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
      rfl z ρ i hi hρi h']
    congr 1
    rw [Work.SSS.faceRestr_eq_ezSimplex p hfib s (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
      (Work.SSS.sigHat σ) rfl i hi h']
    rw [show (ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) s (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ) h')).f (s+t)))
          (Work.SSS.ezElem p s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) z)
        = (ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) s (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ) h' t)) z from
      (Work.SSS.iotaT_eq_ezLinSnd_gen p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
        (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ) h' z).symm]
    rw [show (ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ)).f (s+t)))
          ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) s (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ) h' t)) z)
        = (ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) s (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ) h' t)) z from rfl]
    rw [Work.SSS.iotaF_pieceCastElem p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
      (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ) hρi h' h'' z]
  have hA : (ModuleCat.Hom.hom ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t)))
        (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z i)) = 0 :=
    Work.SSS.grFι_faceB_cycle p hfib s t σ z hz i
  have hcyc : (ModuleCat.Hom.hom ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ).f (s+t))) X) = 0 := by
    rw [← hkey]
    exact hA
  have hxF : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t)))) X = 0 :=
    Work.SSS.IotaChain.iotaF_cycle p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ) h'' z hz
  let m : Work.SSS.coefM p e₀ t :=
    (ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t
      (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom)
      ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
        ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
          ((ComplexShape.down ℕ).next t) rfl hz))
  have hclass : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ)).homologyπ (s+t)
      ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ)).cyclesMk X
        ((ComplexShape.down ℕ).next (s+t)) rfl hxF)
      = c s • (ModuleCat.Hom.hom (Work.SSS.PsiCoef p e₀ hfib hc t s ρ).hom) m :=
    Work.SSS.pieceInv_iotaF_class_b p e₀ hfib hc t c hc1 hal s ρ
      (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) h'' m z hz rfl
  have hmap : (Work.SSS.grF (Work.SSS.Fc p) s).homologyπ (s+t)
        ((Work.SSS.grF (Work.SSS.Fc p) s).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ).f (s+t))) X)
          ((ComplexShape.down ℕ).next (s+t)) rfl hcyc)
      = (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ) (s+t))
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
            (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ)).homologyπ (s+t)
            ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
              (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ)).cyclesMk X
              ((ComplexShape.down ℕ).next (s+t)) rfl hxF)) :=
    Work.SSS.homologyMap_cyclesMk (Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ) rfl X hxF hcyc
  have hcongr : (Work.SSS.grF (Work.SSS.Fc p) s).homologyπ (s+t)
        ((Work.SSS.grF (Work.SSS.Fc p) s).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t)))
            (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
              (Work.SSS.sigHat σ) rfl z i))
          ((ComplexShape.down ℕ).next (s+t)) rfl hA)
      = (Work.SSS.grF (Work.SSS.Fc p) s).homologyπ (s+t)
        ((Work.SSS.grF (Work.SSS.Fc p) s).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ).f (s+t))) X)
          ((ComplexShape.down ℕ).next (s+t)) rfl hcyc) :=
    fcn_homologyπ_cyclesMk_congr hkey hA hcyc
  rw [hcongr, hmap, hclass]
  rw [map_zsmul]

end Work.SSS

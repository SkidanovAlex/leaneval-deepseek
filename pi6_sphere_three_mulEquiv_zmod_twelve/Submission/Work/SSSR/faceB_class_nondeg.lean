import Mathlib
import Submission.Work.SSSR.chainCondAux
import Submission.Work.SSSR.faceRestr_eq_ezSimplex
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `cyclesMk` only depends on the underlying element of the complex. -/
lemma fcn_cyclesMk_congr {K : ChainComplex (ModuleCat R) ℕ} {i : ℕ} {x x' : K.X i} (hxx : x = x')
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
lemma fcn_homologyπ_cyclesMk_congr {K : ChainComplex (ModuleCat R) ℕ} {i : ℕ} {x x' : K.X i}
    (hxx : x = x')
    (hx : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x = 0)
    (hx' : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x' = 0) :
    K.homologyπ i (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)
      = K.homologyπ i (K.cyclesMk x' ((ComplexShape.down ℕ).next i) rfl hx') := by
  rw [fcn_cyclesMk_congr hxx hx hx']

/-- For a nondegenerate face `i ≠ 0` of a nondegenerate `(s+1)`-simplex `σ`, the class of
`(grFι R s)(faceB i)` in `H_{s+t}(grF_s)` is `c s` times the `H(mapPhiY R ρ_i)`-image of
`(PsiCoef ρ_i).hom` of the trivialised class of `z`. -/
theorem faceB_class_nondeg (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSSR.PieceAlpha (R := R) p hfib c)
    (s : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1))
    (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (i : Fin (s+2)) (hi : i ≠ 0)
    (hnd : SimplicialObject.δ (Work.SSSR.sSing B) i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ)
      ∈ (Work.SSSR.sSing B).nonDegenerate s) :
    (Work.SSSR.grF (Work.SSSR.Fc p) s).homologyπ (s+t)
      ((Work.SSSR.grF (Work.SSSR.Fc p) s).cyclesMk
        ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t))
          (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
            (Work.SSSR.sigHat σ) rfl z i)))
        ((ComplexShape.down ℕ).next (s+t)) rfl
        (Work.SSSR.grFι_faceB_cycle p hfib s t σ z hz i))
      = c s • (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
            (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
              ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩)) (s+t))
          ((Work.SSSR.PsiCoef p e₀ hfib hc t s
            (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
              ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩)).hom
            ((Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
              ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
                ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
                  ((ComplexShape.down ℕ).next t) rfl hz)))) := by
  set ρ : Work.SSSR.nIndex (Work.SSSR.sSing B) s :=
    Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
      ⟨SimplicialObject.δ (Work.SSSR.sSing B) i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩
    with hρdef
  have hρi : SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ =
      Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ := by
    rw [hρdef]
    have h := Work.SSSR.nIndexSigma_face σ i hnd
    rw [h]
    congr 1
  have h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ)
      = Work.SSSR.sigmaVert (Work.SSSR.sigHat σ) :=
    Work.SSSR.sigmaVert_face i hi (Work.SSSR.sigHat σ)
  have h'' : Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ)
      = Work.SSSR.sigmaVert (Work.SSSR.sigHat σ) :=
    (congrArg Work.SSSR.sigmaVert hρi).symm.trans h'
  let X : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ)).X (s+t) :=
    (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
      (Work.SSSR.liftFam_proj p hfib) s (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ) h'' t)) z
  have hkey : (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t)))
        (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z i)
      = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ).f (s+t))) X := by
    rw [Work.SSSR.faceB_grFi_nondeg p hfib s t σ (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
      rfl z ρ i hi hρi h']
    congr 1
    rw [Work.SSSR.faceRestr_eq_ezSimplex p hfib s (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
      (Work.SSSR.sigHat σ) rfl i hi h']
    rw [show (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) s (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ) h')).f (s+t)))
          (Work.SSSR.ezElem p s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) z)
        = (ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) s (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ) h' t)) z from
      (Work.SSSR.iotaT_eq_ezLinSnd_gen p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ) h' z).symm]
    rw [show (ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ)).f (s+t)))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) s (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ) h' t)) z)
        = (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) s (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
            (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ) h' t)) z from rfl]
    rw [Work.SSSR.iotaF_pieceCastElem p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
      (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ) hρi h' h'' z]
  have hA : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t)))
        (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z i)) = 0 :=
    Work.SSSR.grFι_faceB_cycle p hfib s t σ z hz i
  have hcyc : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ).f (s+t))) X) = 0 := by
    rw [← hkey]
    exact hA
  have hxF : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t)))) X = 0 :=
    Work.SSSR.IotaChain.iotaF_cycle p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ) h'' z hz
  let m : Work.SSSR.coefM p e₀ t :=
    (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom)
      ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
        ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
          ((ComplexShape.down ℕ).next t) rfl hz))
  have hclass : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ)).homologyπ (s+t)
      ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ)).cyclesMk X
        ((ComplexShape.down ℕ).next (s+t)) rfl hxF)
      = c s • (ModuleCat.Hom.hom (Work.SSSR.PsiCoef p e₀ hfib hc t s ρ).hom) m :=
    Work.SSSR.pieceInv_iotaF_class_b p e₀ hfib hc t c hc1 hal s ρ
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) h'' m z hz rfl
  have hmap : (Work.SSSR.grF (Work.SSSR.Fc p) s).homologyπ (s+t)
        ((Work.SSSR.grF (Work.SSSR.Fc p) s).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ).f (s+t))) X)
          ((ComplexShape.down ℕ).next (s+t)) rfl hcyc)
      = (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ) (s+t))
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ)).homologyπ (s+t)
            ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
              (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ)).cyclesMk X
              ((ComplexShape.down ℕ).next (s+t)) rfl hxF)) :=
    Work.SSSR.homologyMap_cyclesMk (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ) rfl X hxF hcyc
  have hcongr : (Work.SSSR.grF (Work.SSSR.Fc p) s).homologyπ (s+t)
        ((Work.SSSR.grF (Work.SSSR.Fc p) s).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t)))
            (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
              (Work.SSSR.sigHat σ) rfl z i))
          ((ComplexShape.down ℕ).next (s+t)) rfl hA)
      = (Work.SSSR.grF (Work.SSSR.Fc p) s).homologyπ (s+t)
        ((Work.SSSR.grF (Work.SSSR.Fc p) s).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ).f (s+t))) X)
          ((ComplexShape.down ℕ).next (s+t)) rfl hcyc) :=
    fcn_homologyπ_cyclesMk_congr hkey hA hcyc
  rw [hcongr, hmap, hclass]
  rw [map_zsmul]

end Work.SSSR

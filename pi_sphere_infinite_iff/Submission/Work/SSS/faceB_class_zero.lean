import Mathlib
import Submission.Work.SSS.chainCondAux

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `cyclesMk` only depends on the underlying element of the complex. -/
lemma faceBZero_cyclesMk_congr {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ} {x x' : K.X i}
    (hxx : x = x')
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
lemma faceBZero_homologyπ_cyclesMk_congr {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ}
    {x x' : K.X i}
    (hxx : x = x')
    (hx : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x = 0)
    (hx' : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x' = 0) :
    K.homologyπ i (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)
      = K.homologyπ i (K.cyclesMk x' ((ComplexShape.down ℕ).next i) rfl hx') := by
  rw [faceBZero_cyclesMk_congr hxx hx hx']

/-- For the `0`-th face of a nondegenerate `(s+1)`-simplex `σ` (which is nondegenerate and based
at `σ(v₁)`), the class of `(grFι s)(faceB 0)` in `H_{s+t}(grF_s)` is `c s` times the
`H(mapPhiY ρ_0)`-image of `(PsiCoef ρ_0).hom` of the trivialised class of `z`.  Route:
`faceB_grFi_zero` + `homologyMap_cyclesMk` + `ezSimplexZero_chain_class` (with a cycle `z'` over
`σ(v₁)` chosen by `exists_cycleMk` so that `triv (σ(v₁)) [z'] = triv (σ(v₀)) [z]`) +
`iotaF_pieceCastElem` + `pieceInv_iotaF_class_b`. -/
theorem faceB_class_zero (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSS.PieceAlpha p hfib c)
    (s : ℕ) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1))
    (z : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (hnd : SimplicialObject.δ (Work.SSS.sSing B) 0 (Work.SSS.nIndexBase (Work.SSS.sSing B) σ)
      ∈ (Work.SSS.sSing B).nonDegenerate s) :
    (Work.SSS.grF (Work.SSS.Fc p) s).homologyπ (s+t)
      ((Work.SSS.grF (Work.SSS.Fc p) s).cyclesMk
        ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t))
          (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
            (Work.SSS.sigHat σ) rfl z 0)))
        ((ComplexShape.down ℕ).next (s+t)) rfl
        (Work.SSS.grFι_faceB_cycle p hfib s t σ z hz 0))
      = c s • (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
            (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
              ⟨SimplicialObject.δ (Work.SSS.sSing B) 0
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩)) (s+t))
          ((Work.SSS.PsiCoef p e₀ hfib hc t s
            (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
              ⟨SimplicialObject.δ (Work.SSS.sSing B) 0
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩)).hom
            ((Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
              ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
                ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
                  ((ComplexShape.down ℕ).next t) rfl hz)))) := by
  set ρ0 : Work.SSS.nIndex (Work.SSS.sSing B) s :=
    Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
      ⟨SimplicialObject.δ (Work.SSS.sSing B) 0 (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩
    with hρ0def
  have hρ0 : SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ =
      Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0 := by
    rw [hρ0def, Work.SSS.nIndexSigma_face σ 0 hnd]
    congr 1
  -- The two base points of the `0`-face: `σ(v₁) = σ(v₀)` for `ρ0`.
  have hbρ : Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)
      = Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ) :=
    (congrArg Work.SSS.sigmaVert hρ0).symm
  -- The trivialised class of `z`: the `m` of the statement.
  set mt : Work.SSS.coefM p e₀ t :=
    (Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
      ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
        ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
          ((ComplexShape.down ℕ).next t) rfl hz))
    with hmtdef
  -- A cycle over `σ(v₁)` whose `triv`-class is `mt`.
  obtain ⟨z', hz', hz'c⟩ := Work.SSS.exists_cycleMk (Work.SSS.fibreCC p
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))) t
    ((Work.SSS.triv p e₀ hfib hc t
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))).inv mt)
  set mz : Work.SSS.coefM p e₀ t :=
    (Work.SSS.triv p e₀ hfib hc t
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))).hom
      ((Work.SSS.fibreCC p
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))).homologyπ t
        ((Work.SSS.fibreCC p
          (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))).cyclesMk z'
          ((ComplexShape.down ℕ).next t) rfl hz'))
    with hmzdef
  have hmz : mz = mt := by
    rw [hmzdef, ← hz'c]
    have h := congrArg (fun (f : Work.SSS.coefM p e₀ t ⟶ Work.SSS.coefM p e₀ t) =>
      ModuleCat.Hom.hom f mt)
      (Iso.inv_hom_id (Work.SSS.triv p e₀ hfib hc t
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))))
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h
  -- The chain of the `0`-face lift `ezSimplexZero`, in the `(δ 0 ≫ σ)`-piece.
  set xQ : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).X (s+t) :=
    (ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).f (s+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplexZero p
          (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
          (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl)).f (s+t)))
        (Work.SSS.ezElem p s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) z))
    with hxQdef
  -- `grFι (faceB 0)` is `mapPhiY ρ0` of (the transport of) that chain.
  have hface : (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t)))
        (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z 0)
      = (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ0).f (s+t)))
          (Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0 xQ) :=
    Work.SSS.faceB_grFi_zero p hfib s t σ
      (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) rfl z ρ0 hρ0
  have hA : (ModuleCat.Hom.hom ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t)))
        (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z 0)) = 0 :=
    Work.SSS.grFι_faceB_cycle p hfib s t σ z hz 0
  have hcyc : (ModuleCat.Hom.hom ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ0).f (s+t)))
        (Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0 xQ)) = 0 := by
    rw [← hface]
    exact hA
  -- The two chains are cycles in the `(δ 0 ≫ σ)`-piece.
  have hxQ : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t)))) xQ = 0 :=
    Work.SSS.ezLinSnd_chain_cycle p s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)
      (Work.SSS.ezSimplexZero p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl)
      (Work.SSS.ezSimplexZero_fst (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl)
      z hz
  have hXP : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      (Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0 xQ) = 0 := by
    rw [Work.SSS.d_pieceCastElem (Work.SSS.sSingP p) hρ0 xQ, hxQ]
    rw [Work.SSS.pieceCastElem_zero]
  -- The canonical chain over `σ(v₁)`, the `ezSimplex`-lift of the same face.
  set LQ : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).X (s+t) :=
    (ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).f (s+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p
          (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
          (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
          (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ) rfl)).f (s+t)))
        (Work.SSS.ezLinSnd s t (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p
            (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))))
          (Work.SSS.stdIdSimplex s) z'))
    with hLQdef
  have hLQ : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t)))) LQ = 0 :=
    Work.SSS.ezLinSnd_chain_cycle p s t
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)
      (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ) rfl)
      (Work.SSS.ezSimplex_fst (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ) rfl)
      z' hz'
  -- The chain-level input: the two chains have the same class in the piece.
  have hclass_Q : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).homologyπ (s+t)
      ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).cyclesMk xQ
        ((ComplexShape.down ℕ).next (s+t)) rfl hxQ)
      = (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).homologyπ (s+t)
      ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).cyclesMk LQ
        ((ComplexShape.down ℕ).next (s+t)) rfl hLQ) :=
    Work.SSS.ezSimplexZero_chain_class p e₀ hfib hc s t
      (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z hz z' hz'
      hxQ hLQ hmz
  -- The `ezSimplex`-chain is the `iotaF`-value of `z'`.
  set iF : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).X (s+t) :=
    (ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
      (Work.SSS.liftFam_proj p hfib) s
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0) hbρ t)) z'
    with hiFdef
  have hcycI : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t)))) iF = 0 :=
    Work.SSS.IotaChain.iotaF_cycle p hfib s t
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0) hbρ z' hz'
  have hLQ_iota : LQ = (ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
      (Work.SSS.liftFam_proj p hfib) s
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ) rfl t)) z' := by
    rw [hLQdef]
    simp only [Work.SSS.iotaF]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, Work.SSS.iotaT_eq_ezLinSnd_gen]
  have hcastL : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      (Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0 LQ) = 0 := by
    rw [Work.SSS.d_pieceCastElem (Work.SSS.sSingP p) hρ0 LQ, hLQ]
    rw [Work.SSS.pieceCastElem_zero]
  have hcastL_iota : Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0 LQ = iF := by
    rw [hLQ_iota]
    exact Work.SSS.iotaF_pieceCastElem p hfib s t
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0) hρ0 rfl hbρ z'
  have ht1 := Work.SSS.homologyπ_cyclesMk_pieceCastElem (Work.SSS.sSingP p) hρ0 xQ hxQ hXP
  have ht3 := Work.SSS.homologyπ_cyclesMk_pieceCastElem (Work.SSS.sSingP p) hρ0 LQ hLQ hcastL
  -- The `rho0`-piece class of the `iotaF`-value, by the (inverse) sign spec.
  have hclass_P : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).homologyπ (s+t)
      ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).cyclesMk iF
        ((ComplexShape.down ℕ).next (s+t)) rfl hcycI)
      = c s • (ModuleCat.Hom.hom (Work.SSS.PsiCoef p e₀ hfib hc t s ρ0).hom) mt := by
    rw [← hmz]
    exact Work.SSS.pieceInv_iotaF_class_b p e₀ hfib hc t c hc1 hal s ρ0
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)) hbρ mz z' hz' rfl
  -- Final assembly.
  have hcastL_hπ : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).homologyπ (s+t)
      ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).cyclesMk
        (Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0 LQ)
        ((ComplexShape.down ℕ).next (s+t)) rfl hcastL)
      = (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).homologyπ (s+t)
      ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).cyclesMk iF
        ((ComplexShape.down ℕ).next (s+t)) rfl hcycI) :=
    faceBZero_homologyπ_cyclesMk_congr hcastL_iota hcastL hcycI
  -- The two transports of `ht1`/`ht3` and the chain equality.
  have hclass : (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).homologyπ (s+t)
      ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)).cyclesMk
        (Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0 xQ)
        ((ComplexShape.down ℕ).next (s+t)) rfl hXP)
      = c s • (ModuleCat.Hom.hom (Work.SSS.PsiCoef p e₀ hfib hc t s ρ0).hom) mt := by
    rw [ht1, hclass_Q, ← ht3, hcastL_hπ]
    exact hclass_P
  have hcongr := faceBZero_homologyπ_cyclesMk_congr hface hA hcyc
  have hmap := Work.SSS.homologyMap_cyclesMk (Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ0)
    rfl (Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0 xQ) hXP hcyc
  rw [hcongr, hmap, hclass]
  rw [map_zsmul]

end Work.SSS

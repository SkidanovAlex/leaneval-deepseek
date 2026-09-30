import Mathlib
import Submission.Work.SSSR.chainCondAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `cyclesMk` only depends on the underlying element of the complex. -/
lemma faceBZero_cyclesMk_congr {K : ChainComplex (ModuleCat R) ℕ} {i : ℕ} {x x' : K.X i}
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
lemma faceBZero_homologyπ_cyclesMk_congr {K : ChainComplex (ModuleCat R) ℕ} {i : ℕ}
    {x x' : K.X i}
    (hxx : x = x')
    (hx : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x = 0)
    (hx' : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) x' = 0) :
    K.homologyπ i (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)
      = K.homologyπ i (K.cyclesMk x' ((ComplexShape.down ℕ).next i) rfl hx') := by
  rw [faceBZero_cyclesMk_congr hxx hx hx']

/-- For the `0`-th face of a nondegenerate `(s+1)`-simplex `σ` (which is nondegenerate and based
at `σ(v₁)`), the class of `(grFι R s)(faceB 0)` in `H_{s+t}(grF_s)` is `c s` times the
`H(mapPhiY R ρ_0)`-image of `(PsiCoef ρ_0).hom` of the trivialised class of `z`.  Route:
`faceB_grFi_zero` + `homologyMap_cyclesMk` + `ezSimplexZero_chain_class` (with a cycle `z'` over
`σ(v₁)` chosen by `exists_cycleMk` so that `triv (σ(v₁)) [z'] = triv (σ(v₀)) [z]`) +
`iotaF_pieceCastElem` + `pieceInv_iotaF_class_b`. -/
theorem faceB_class_zero (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSSR.PieceAlpha (R := R) p hfib c)
    (s : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1))
    (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (hnd : SimplicialObject.δ (Work.SSSR.sSing B) 0 (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ)
      ∈ (Work.SSSR.sSing B).nonDegenerate s) :
    (Work.SSSR.grF (Work.SSSR.Fc p) s).homologyπ (s+t)
      ((Work.SSSR.grF (Work.SSSR.Fc p) s).cyclesMk
        ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t))
          (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
            (Work.SSSR.sigHat σ) rfl z 0)))
        ((ComplexShape.down ℕ).next (s+t)) rfl
        (Work.SSSR.grFι_faceB_cycle p hfib s t σ z hz 0))
      = c s • (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
            (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
              ⟨SimplicialObject.δ (Work.SSSR.sSing B) 0
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩)) (s+t))
          ((Work.SSSR.PsiCoef p e₀ hfib hc t s
            (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
              ⟨SimplicialObject.δ (Work.SSSR.sSing B) 0
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩)).hom
            ((Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
              ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
                ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
                  ((ComplexShape.down ℕ).next t) rfl hz)))) := by
  set ρ0 : Work.SSSR.nIndex (Work.SSSR.sSing B) s :=
    Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
      ⟨SimplicialObject.δ (Work.SSSR.sSing B) 0 (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩
    with hρ0def
  have hρ0 : SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ =
      Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0 := by
    rw [hρ0def, Work.SSSR.nIndexSigma_face σ 0 hnd]
    congr 1
  -- The two base points of the `0`-face: `σ(v₁) = σ(v₀)` for `ρ0`.
  have hbρ : Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)
      = Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ) :=
    (congrArg Work.SSSR.sigmaVert hρ0).symm
  -- The trivialised class of `z`: the `m` of the statement.
  set mt : Work.SSSR.coefM p e₀ t :=
    (Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
      ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
        ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
          ((ComplexShape.down ℕ).next t) rfl hz))
    with hmtdef
  -- A cycle over `σ(v₁)` whose `triv`-class is `mt`.
  obtain ⟨z', hz', hz'c⟩ := Work.SSSR.exists_cycleMk (Work.SSSR.fibreCC p
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))) t
    ((Work.SSSR.triv p e₀ hfib hc t
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))).inv mt)
  set mz : Work.SSSR.coefM p e₀ t :=
    (Work.SSSR.triv p e₀ hfib hc t
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))).hom
      ((Work.SSSR.fibreCC p
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))).homologyπ t
        ((Work.SSSR.fibreCC p
          (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))).cyclesMk z'
          ((ComplexShape.down ℕ).next t) rfl hz'))
    with hmzdef
  have hmz : mz = mt := by
    rw [hmzdef, ← hz'c]
    have h := congrArg (fun (f : Work.SSSR.coefM p e₀ t ⟶ Work.SSSR.coefM p e₀ t) =>
      ModuleCat.Hom.hom f mt)
      (Iso.inv_hom_id (Work.SSSR.triv p e₀ hfib hc t
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))))
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h
  -- The chain of the `0`-face lift `ezSimplexZero`, in the `(δ 0 ≫ σ)`-piece.
  set xQ : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).X (s+t) :=
    (ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).f (s+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplexZero p
          (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl)).f (s+t)))
        (Work.SSSR.ezElem p s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) z))
    with hxQdef
  -- `grFι R (faceB 0)` is `mapPhiY R ρ0` of (the transport of) that chain.
  have hface : (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t)))
        (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z 0)
      = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ0).f (s+t)))
          (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0 xQ) :=
    Work.SSSR.faceB_grFi_zero p hfib s t σ
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) rfl z ρ0 hρ0
  have hA : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t)))
        (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z 0)) = 0 :=
    Work.SSSR.grFι_faceB_cycle p hfib s t σ z hz 0
  have hcyc : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ0).f (s+t)))
        (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0 xQ)) = 0 := by
    rw [← hface]
    exact hA
  -- The two chains are cycles in the `(δ 0 ≫ σ)`-piece.
  have hxQ : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t)))) xQ = 0 :=
    Work.SSSR.ezLinSnd_chain_cycle p s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)
      (Work.SSSR.ezSimplexZero p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl)
      (Work.SSSR.ezSimplexZero_fst (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl)
      z hz
  have hXP : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0 xQ) = 0 := by
    rw [Work.SSSR.d_pieceCastElem (Work.SSSR.sSingP p) hρ0 xQ, hxQ]
    rw [Work.SSSR.pieceCastElem_zero]
  -- The canonical chain over `σ(v₁)`, the `ezSimplex`-lift of the same face.
  set LQ : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).X (s+t) :=
    (ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).f (s+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p
          (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
          (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
          (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ) rfl)).f (s+t)))
        (Work.SSSR.ezLinSnd s t (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
            (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))))
          (Work.SSSR.stdIdSimplex s) z'))
    with hLQdef
  have hLQ : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t)))) LQ = 0 :=
    Work.SSSR.ezLinSnd_chain_cycle p s t
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)
      (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ) rfl)
      (Work.SSSR.ezSimplex_fst (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ) rfl)
      z' hz'
  -- The chain-level input: the two chains have the same class in the piece.
  have hclass_Q : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).homologyπ (s+t)
      ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).cyclesMk xQ
        ((ComplexShape.down ℕ).next (s+t)) rfl hxQ)
      = (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).homologyπ (s+t)
      ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).cyclesMk LQ
        ((ComplexShape.down ℕ).next (s+t)) rfl hLQ) :=
    Work.SSSR.ezSimplexZero_chain_class p e₀ hfib hc s t
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z hz z' hz'
      hxQ hLQ hmz
  -- The `ezSimplex`-chain is the `iotaF`-value of `z'`.
  set iF : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).X (s+t) :=
    (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
      (Work.SSSR.liftFam_proj p hfib) s
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0) hbρ t)) z'
    with hiFdef
  have hcycI : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t)))) iF = 0 :=
    Work.SSSR.IotaChain.iotaF_cycle p hfib s t
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0) hbρ z' hz'
  have hLQ_iota : LQ = (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
      (Work.SSSR.liftFam_proj p hfib) s
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ) rfl t)) z' := by
    rw [hLQdef]
    simp only [Work.SSSR.iotaF]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, Work.SSSR.iotaT_eq_ezLinSnd_gen]
  have hcastL : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).d (s+t)
      ((ComplexShape.down ℕ).next (s+t))))
      (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0 LQ) = 0 := by
    rw [Work.SSSR.d_pieceCastElem (Work.SSSR.sSingP p) hρ0 LQ, hLQ]
    rw [Work.SSSR.pieceCastElem_zero]
  have hcastL_iota : Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0 LQ = iF := by
    rw [hLQ_iota]
    exact Work.SSSR.iotaF_pieceCastElem p hfib s t
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0) hρ0 rfl hbρ z'
  have ht1 := Work.SSSR.homologyπ_cyclesMk_pieceCastElem (Work.SSSR.sSingP p) hρ0 xQ hxQ hXP
  have ht3 := Work.SSSR.homologyπ_cyclesMk_pieceCastElem (Work.SSSR.sSingP p) hρ0 LQ hLQ hcastL
  -- The `rho0`-piece class of the `iotaF`-value, by the (inverse) sign spec.
  have hclass_P : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).homologyπ (s+t)
      ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).cyclesMk iF
        ((ComplexShape.down ℕ).next (s+t)) rfl hcycI)
      = c s • (ModuleCat.Hom.hom (Work.SSSR.PsiCoef p e₀ hfib hc t s ρ0).hom) mt := by
    rw [← hmz]
    exact Work.SSSR.pieceInv_iotaF_class_b p e₀ hfib hc t c hc1 hal s ρ0
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)) hbρ mz z' hz' rfl
  -- Final assembly.
  have hcastL_hπ : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).homologyπ (s+t)
      ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).cyclesMk
        (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0 LQ)
        ((ComplexShape.down ℕ).next (s+t)) rfl hcastL)
      = (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).homologyπ (s+t)
      ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).cyclesMk iF
        ((ComplexShape.down ℕ).next (s+t)) rfl hcycI) :=
    faceBZero_homologyπ_cyclesMk_congr hcastL_iota hcastL hcycI
  -- The two transports of `ht1`/`ht3` and the chain equality.
  have hclass : (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).homologyπ (s+t)
      ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)).cyclesMk
        (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0 xQ)
        ((ComplexShape.down ℕ).next (s+t)) rfl hXP)
      = c s • (ModuleCat.Hom.hom (Work.SSSR.PsiCoef p e₀ hfib hc t s ρ0).hom) mt := by
    rw [ht1, hclass_Q, ← ht3, hcastL_hπ]
    exact hclass_P
  have hcongr := faceBZero_homologyπ_cyclesMk_congr hface hA hcyc
  have hmap := Work.SSSR.homologyMap_cyclesMk (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ0)
    rfl (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0 xQ) hXP hcyc
  rw [hcongr, hmap, hclass]
  rw [map_zsmul]

end Work.SSSR

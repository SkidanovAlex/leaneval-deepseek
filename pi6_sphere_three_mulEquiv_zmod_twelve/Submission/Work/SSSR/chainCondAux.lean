import Mathlib
import Submission.Work.SSSR.serreE1CruxD1
import Submission.Work.SSSR.faceB_grFi_nondeg
import Submission.Work.SSSR.faceB_grFi_degenerate
import Submission.Work.SSSR.faceB_grFi_zero
import Submission.Work.SSSR.iotaF_pieceCastElem
import Submission.Work.SSSR.ezSimplexZero_chain_class
import Submission.Work.SSSR.jF_eq_grFi
import Submission.Work.SSSR.faceD_iota
import Submission.Work.SSSR.nIndexSigma_face
import Submission.Work.SSSR.exists_cycleMk
import Submission.Work.SSSR.cyclesMk_sum
import Submission.Work.SSSR.d_sndToR_iotaTLin
import Submission.Work.SSSR.homologyMap_cyclesMk
import Submission.Work.SSSR.faceB_grFi_nondeg
import Submission.Work.SSSR.faceB_grFi_zero
import Submission.Work.SSSR.faceB_grFi_degenerate
import Submission.Work.SSSR.nIndexSigma_face
import Submission.Work.SSSR.sigmaVert_face
import Submission.Work.SSSR.ezLinSnd_chain_cycle
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]


namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The pointwise evaluation of a `ℤ`-multiple of a morphism of `ℤ`-modules. -/
lemma zsmul_hom_apply {M N : ModuleCat R} (a : ℤ) (f : M ⟶ N) (m : M) :
    (a • ModuleCat.Hom.hom f) m = a • ModuleCat.Hom.hom f m := rfl


/-- The general form of `Work.SSSR.iotaT_eq_iotaTLin`: `iotaT` evaluated on a chain is the
Eilenberg–Zilber shuffle chain `ezLinSnd` pushed into the pullback by the coherent lift. -/
theorem iotaT_eq_ezLinSnd_gen (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (P t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (z : (Work.SSSR.fibreCC p b).X t) :
    (ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) P b σ h t)) z
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) P b σ h)).f (P+t)))
          (Work.SSSR.ezLinSnd P t (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P) z) := by
  have hmap : Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) P b σ h t
      = Work.SSSR.ezLinSnd P t (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P)
        ≫ (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) P b σ h)).f (P+t) := by
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [Work.SSSR.iotaT_gen, ← Category.assoc]
    rw [Work.SSSR.ezLinSnd_ι, ← Work.SSSR.eltHom_comp]
    congr 1
  rw [hmap, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The transport `Work.SSSR.pieceCastElem` commutes with the differential. -/
lemma d_pieceCastElem {X Y : SSet.{0}} (f : X ⟶ Y) {P n j : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m')
    (x : (Work.SSSR.pieceAlong R f m).X n) :
    (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R f m').d n j)) (Work.SSSR.pieceCastElem f h x)
      = Work.SSSR.pieceCastElem f h
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R f m).d n j)) x) := by
  subst h
  simp only [Work.SSSR.pieceCastElem, eqToHom_refl, ModuleCat.id_apply]

/-- The transport `Work.SSSR.pieceCastElem` commutes with `homologyπ` on cycle classes. -/
lemma homologyπ_cyclesMk_pieceCastElem {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m')
    (x : (Work.SSSR.pieceAlong R f m).X n)
    (hx : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R f m).d n
      ((ComplexShape.down ℕ).next n))) x = 0)
    (hx' : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R f m').d n
      ((ComplexShape.down ℕ).next n))) (Work.SSSR.pieceCastElem f h x) = 0) :
    (Work.SSSR.pieceAlong R f m').homologyπ n
        ((Work.SSSR.pieceAlong R f m').cyclesMk (Work.SSSR.pieceCastElem f h x)
          ((ComplexShape.down ℕ).next n) rfl hx')
      = eqToHom (congrArg (fun m => (Work.SSSR.pieceAlong R f m).homology n) h)
          ((Work.SSSR.pieceAlong R f m).homologyπ n
            ((Work.SSSR.pieceAlong R f m).cyclesMk x ((ComplexShape.down ℕ).next n) rfl hx)) := by
  subst h
  simp only [Work.SSSR.pieceCastElem, eqToHom_refl, ModuleCat.id_apply]

/-- **The `∂ ⊗ id` side on the generator `[σ] ⊗ m`.**  The alternating-face differential
`Work.SSSR.faceD'` followed by `Work.SSSR.PsiSig` sends `m` to the alternating sum of the
`H(mapPhiY R ρ_i)`-images of `(PsiCoef ρ_i).hom m`, over the nondegenerate faces `ρ_i`. -/
theorem faceD_PsiSig_gen (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) (s : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1)) (m : Work.SSSR.coefM p e₀ t) :
    (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
        Work.SSSR.coefM p e₀ t) σ ≫
        (Work.SSSR.faceD' (Work.SSSR.sSing B) (Work.SSSR.coefM p e₀ t) s ≫
          Work.SSSR.PsiSig p e₀ hfib hc t s))) m
      = ∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : (Work.SSSR.sSing B).δ i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ)
              ∈ (Work.SSSR.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨(Work.SSSR.sSing B).δ i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t))
                ((Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨(Work.SSSR.sSing B).δ i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom m)
           else 0) := by
  have hstep : Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
        Work.SSSR.coefM p e₀ t) σ ≫
        (Work.SSSR.faceD' (Work.SSSR.sSing B) (Work.SSSR.coefM p e₀ t) s ≫
          Work.SSSR.PsiSig p e₀ hfib hc t s)
      = ∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : (Work.SSSR.sSing B).δ i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ)
              ∈ (Work.SSSR.sSing B).nonDegenerate s
           then (Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨(Work.SSSR.sSing B).δ i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom ≫
                HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨(Work.SSSR.sSing B).δ i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t)
           else 0) := by
    rw [← Category.assoc, Work.SSSR.faceD_iota, CategoryTheory.Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [CategoryTheory.Preadditive.zsmul_comp]
    congr 1
    split_ifs with h
    · exact Work.SSSR.Sigma_ι_comp_PsiSig p e₀ hfib hc t s _
    · rw [zero_comp]
  rw [hstep, ModuleCat.hom_sum]
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ModuleCat.hom_zsmul, zsmul_hom_apply]
  congr 1
  by_cases h : (Work.SSSR.sSing B).δ i (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ)
      ∈ (Work.SSSR.sSing B).nonDegenerate s
  · rw [dif_pos h, dif_pos h, ModuleCat.hom_comp, LinearMap.comp_apply]
  · rw [dif_neg h, dif_neg h]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

/-- **The class of the Eilenberg–Zilber chain of a cycle is `c n` times `(PsiCoef n ρ).hom m`**,
whenever `m` is the trivialised class of `z`.  This is the inverse form of the sign spec
`Work.SSSR.PieceInv`, transported through the trivialisation `Work.SSSR.triv`. -/
theorem pieceInv_iotaF_class (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSSR.PieceAlpha (R := R) p hfib c)
    (n : ℕ) (ρ : Work.SSSR.nIndex (Work.SSSR.sSing B) n) (m : Work.SSSR.coefM p e₀ t)
    (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p
        (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (hm : (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t
        (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).hom)
        ((Work.SSSR.fibreCC p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).homologyπ t
          ((Work.SSSR.fibreCC p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz)) = m) :
    (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ)).homologyπ (n+t)
        ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ)).cyclesMk
          ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) n
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ) rfl t)) z)
          ((ComplexShape.down ℕ).next (n+t)) rfl
          (Work.SSSR.IotaChain.iotaF_cycle p hfib n t
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ) rfl z hz))
      = c n • ((Work.SSSR.PsiCoef p e₀ hfib hc t n ρ).hom m) := by
  have hcyc := Work.SSSR.IotaChain.iotaF_cycle p hfib n t
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ) rfl z hz
  have hPI := Work.SSSR.pieceInv_of_pieceAlpha p hfib c hc1 hal n t
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ) z hz hcyc
  -- the trivialisation sends `m` back to the class of `z`
  have hzh : (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).inv) m
      = (Work.SSSR.fibreCC p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).homologyπ t
          ((Work.SSSR.fibreCC p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz) := by
    rw [← hm]
    have hcomp := Iso.hom_inv_id (Work.SSSR.triv (R := R) p e₀ hfib hc t
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ)))
    have hx := congrArg (fun f => (ConcreteCategory.hom f)
        ((Work.SSSR.fibreCC p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).homologyπ t
          ((Work.SSSR.fibreCC p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz))) hcomp
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using hx
  have hPsi : (Work.SSSR.PsiCoef p e₀ hfib hc t n ρ).hom m
      = (ModuleCat.Hom.hom (Work.SSSR.serreE1PieceIso p hfib n t
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ)).inv)
          ((Work.SSSR.fibreCC p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).homologyπ t
            ((Work.SSSR.fibreCC p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ))).cyclesMk z
              ((ComplexShape.down ℕ).next t) rfl hz)) := by
    simp only [Work.SSSR.PsiCoef, Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    rw [hzh]
  have hcc : c n * c n = 1 := by
    rcases hc1 n with h' | h' <;> rw [h'] <;> norm_num
  rw [hPsi, hPI, smul_smul, hcc, one_smul]


/-- `pieceInv_iotaF_class` with the fibre base point `b` kept as an explicit variable
(`hb : sigmaVert (nIndexSigma n ρ) = b`). -/
theorem pieceInv_iotaF_class_b (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSSR.PieceAlpha (R := R) p hfib c)
    (n : ℕ) (ρ : Work.SSSR.nIndex (Work.SSSR.sSing B) n) (b : B)
    (hb : Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ) = b)
    (m : Work.SSSR.coefM p e₀ t)
    (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
    (hm : (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t b).hom)
        ((Work.SSSR.fibreCC p b).homologyπ t
          ((Work.SSSR.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz)) = m) :
    (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ)).homologyπ (n+t)
        ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ)).cyclesMk
          ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) n b (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ) hb t)) z)
          ((ComplexShape.down ℕ).next (n+t)) rfl
          (Work.SSSR.IotaChain.iotaF_cycle p hfib n t b
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n ρ) hb z hz))
      = c n • ((Work.SSSR.PsiCoef p e₀ hfib hc t n ρ).hom m) := by
  subst b
  exact pieceInv_iotaF_class p e₀ hfib hc t c hc1 hal n ρ m z hz hm

/-- Transport of `0` along `pieceCastElem`. -/
lemma pieceCastElem_zero {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m') :
    Work.SSSR.pieceCastElem f h (0 : (Work.SSSR.pieceAlong R f m).X n) = 0 := by
  subst h
  simp only [Work.SSSR.pieceCastElem, eqToHom_refl, ModuleCat.id_apply, LinearMap.id_apply]

/-- The face chain `faceB i`, pushed to the graded piece `grF_s`, is a cycle. -/
lemma grFι_faceB_cycle (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s t : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1))
    (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (i : Fin (s+2)) :
    (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t)
        ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t))
        (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z i))) = 0 := by
  by_cases hnd : SimplicialObject.δ (Work.SSSR.sSing B) i
      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
  · by_cases hi : i = 0
    · subst hi
      have hρ0 : SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ
          = Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s
              (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                ⟨SimplicialObject.δ (Work.SSSR.sSing B) 0
                  (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩) :=
        Work.SSSR.nIndexSigma_face σ 0 hnd
      rw [Work.SSSR.faceB_grFi_zero p hfib s t σ (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) rfl z _ hρ0]
      rw [Work.SSSR.chainMap_comm_apply_elem
        (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
          (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
              ⟨SimplicialObject.δ (Work.SSSR.sSing B) 0
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩)) _]
      rw [Work.SSSR.d_pieceCastElem]
      simp only [Work.SSSR.ezElem]
      rw [Work.SSSR.ezLinSnd_chain_cycle p s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)
        (Work.SSSR.ezSimplexZero p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl)
        (by simp) z hz]
      rw [pieceCastElem_zero]
      exact map_zero _
    · have hρi : SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ
          = Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s
              (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                  (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩) :=
        Work.SSSR.nIndexSigma_face σ i hnd
      have h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ)
          = Work.SSSR.sigmaVert (Work.SSSR.sigHat σ) :=
        Work.SSSR.sigmaVert_face i hi (Work.SSSR.sigHat σ)
      rw [Work.SSSR.faceB_grFi_nondeg p hfib s t σ (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) rfl z
        _ i hi hρi h']
      rw [Work.SSSR.chainMap_comm_apply_elem
        (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
          (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
              ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), hnd⟩)) _]
      rw [Work.SSSR.d_pieceCastElem]
      simp only [Work.SSSR.ezElem]
      rw [Work.SSSR.ezLinSnd_chain_cycle p s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ)
        (Work.SSSR.faceRestr p hfib s (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl i)
        (by
          rw [Work.SSSR.faceRestr]
          exact Work.SSSR.faceLift_fst (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ) _ _ i) z hz]
      rw [pieceCastElem_zero]
      exact map_zero _
  · cases s with
    | zero =>
      rw [SSet.nondegenerate_zero] at hnd
      exact absurd (Set.mem_univ _) hnd
    | succ k =>
      rw [Work.SSSR.faceB_grFi_degenerate p hfib k t σ z i hnd]
      exact map_zero _


/-- `cyclesMk` of `0` is `0`. -/
lemma cyclesMk_zero {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j)
    (h : (ModuleCat.Hom.hom (K.d i j)) (0 : K.X i) = 0) :
    K.cyclesMk (0 : K.X i) j hj h = 0 := by
  apply (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance
  simp only [map_zero]
  exact HomologicalComplex.i_cyclesMk (K := K) (0 : K.X i) j hj h

/-- The two spellings of the underlying function of a morphism of `ℤ`-modules agree. -/
lemma ccHom {M N : ModuleCat R} (f : M ⟶ N) :
    CategoryTheory.ConcreteCategory.hom f = ModuleCat.Hom.hom f := rfl

/-- The underlying function of a morphism of `ℤ`-modules, through the forgetful functor to `Ab`. -/
lemma ccHomF {M N : ModuleCat R} (f : M ⟶ N) :
    CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat R) Ab).map f)
      = ModuleCat.Hom.hom f := rfl

end Work.SSSR

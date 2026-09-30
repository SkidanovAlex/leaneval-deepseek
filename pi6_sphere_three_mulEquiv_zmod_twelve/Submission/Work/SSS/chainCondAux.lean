import Mathlib
import Submission.Work.SSS.serreE1CruxD1
import Submission.Work.SSS.faceB_grFi_nondeg
import Submission.Work.SSS.faceB_grFi_degenerate
import Submission.Work.SSS.faceB_grFi_zero
import Submission.Work.SSS.iotaF_pieceCastElem
import Submission.Work.SSS.ezSimplexZero_chain_class
import Submission.Work.SSS.jF_eq_grFi
import Submission.Work.SSS.faceD_iota
import Submission.Work.SSS.nIndexSigma_face
import Submission.Work.SSS.exists_cycleMk
import Submission.Work.SSS.cyclesMk_sum
import Submission.Work.SSS.d_sndToR_iotaTLin
import Submission.Work.SSS.homologyMap_cyclesMk
import Submission.Work.SSS.faceB_grFi_nondeg
import Submission.Work.SSS.faceB_grFi_zero
import Submission.Work.SSS.faceB_grFi_degenerate
import Submission.Work.SSS.nIndexSigma_face
import Submission.Work.SSS.sigmaVert_face
import Submission.Work.SSS.ezLinSnd_chain_cycle


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

/-- The pointwise evaluation of a `ℤ`-multiple of a morphism of `ℤ`-modules. -/
lemma zsmul_hom_apply {M N : ModuleCat ℤ} (a : ℤ) (f : M ⟶ N) (m : M) :
    (a • ModuleCat.Hom.hom f) m = a • ModuleCat.Hom.hom f m := rfl


/-- The general form of `Work.SSS.iotaT_eq_iotaTLin`: `iotaT` evaluated on a chain is the
Eilenberg–Zilber shuffle chain `ezLinSnd` pushed into the pullback by the coherent lift. -/
theorem iotaT_eq_ezLinSnd_gen (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (P t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (z : (Work.SSS.fibreCC p b).X t) :
    (ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) P b σ h t)) z
      = (ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) P b σ h)).f (P+t)))
          (Work.SSS.ezLinSnd P t (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
            (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) z) := by
  have hmap : Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) P b σ h t
      = Work.SSS.ezLinSnd P t (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P)
        ≫ (Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) P b σ h)).f (P+t) := by
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [Work.SSS.iotaT_gen, ← Category.assoc]
    rw [Work.SSS.ezLinSnd_ι, ← Work.SSS.eltHom_comp]
    congr 1
  rw [hmap, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The transport `Work.SSS.pieceCastElem` commutes with the differential. -/
lemma d_pieceCastElem {X Y : SSet.{0}} (f : X ⟶ Y) {P n j : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m')
    (x : (Work.SSS.pieceAlong f m).X n) :
    (ModuleCat.Hom.hom ((Work.SSS.pieceAlong f m').d n j)) (Work.SSS.pieceCastElem f h x)
      = Work.SSS.pieceCastElem f h
          ((ModuleCat.Hom.hom ((Work.SSS.pieceAlong f m).d n j)) x) := by
  subst h
  simp only [Work.SSS.pieceCastElem, eqToHom_refl, ModuleCat.id_apply]

/-- The transport `Work.SSS.pieceCastElem` commutes with `homologyπ` on cycle classes. -/
lemma homologyπ_cyclesMk_pieceCastElem {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m')
    (x : (Work.SSS.pieceAlong f m).X n)
    (hx : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong f m).d n
      ((ComplexShape.down ℕ).next n))) x = 0)
    (hx' : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong f m').d n
      ((ComplexShape.down ℕ).next n))) (Work.SSS.pieceCastElem f h x) = 0) :
    (Work.SSS.pieceAlong f m').homologyπ n
        ((Work.SSS.pieceAlong f m').cyclesMk (Work.SSS.pieceCastElem f h x)
          ((ComplexShape.down ℕ).next n) rfl hx')
      = eqToHom (congrArg (fun m => (Work.SSS.pieceAlong f m).homology n) h)
          ((Work.SSS.pieceAlong f m).homologyπ n
            ((Work.SSS.pieceAlong f m).cyclesMk x ((ComplexShape.down ℕ).next n) rfl hx)) := by
  subst h
  simp only [Work.SSS.pieceCastElem, eqToHom_refl, ModuleCat.id_apply]

/-- **The `∂ ⊗ id` side on the generator `[σ] ⊗ m`.**  The alternating-face differential
`Work.SSS.faceD'` followed by `Work.SSS.PsiSig` sends `m` to the alternating sum of the
`H(mapPhiY ρ_i)`-images of `(PsiCoef ρ_i).hom m`, over the nondegenerate faces `ρ_i`. -/
theorem faceD_PsiSig_gen (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) (s : ℕ)
    (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1)) (m : Work.SSS.coefM p e₀ t) :
    (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
        Work.SSS.coefM p e₀ t) σ ≫
        (Work.SSS.faceD' (Work.SSS.sSing B) (Work.SSS.coefM p e₀ t) s ≫
          Work.SSS.PsiSig p e₀ hfib hc t s))) m
      = ∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : (Work.SSS.sSing B).δ i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ)
              ∈ (Work.SSS.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨(Work.SSS.sSing B).δ i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t))
                ((Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨(Work.SSS.sSing B).δ i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom m)
           else 0) := by
  have hstep : Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
        Work.SSS.coefM p e₀ t) σ ≫
        (Work.SSS.faceD' (Work.SSS.sSing B) (Work.SSS.coefM p e₀ t) s ≫
          Work.SSS.PsiSig p e₀ hfib hc t s)
      = ∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : (Work.SSS.sSing B).δ i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ)
              ∈ (Work.SSS.sSing B).nonDegenerate s
           then (Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨(Work.SSS.sSing B).δ i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom ≫
                HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨(Work.SSS.sSing B).δ i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t)
           else 0) := by
    rw [← Category.assoc, Work.SSS.faceD_iota, CategoryTheory.Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [CategoryTheory.Preadditive.zsmul_comp]
    congr 1
    split_ifs with h
    · exact Work.SSS.Sigma_ι_comp_PsiSig p e₀ hfib hc t s _
    · rw [zero_comp]
  rw [hstep, ModuleCat.hom_sum]
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ModuleCat.hom_zsmul, zsmul_hom_apply]
  congr 1
  by_cases h : (Work.SSS.sSing B).δ i (Work.SSS.nIndexBase (Work.SSS.sSing B) σ)
      ∈ (Work.SSS.sSing B).nonDegenerate s
  · rw [dif_pos h, dif_pos h, ModuleCat.hom_comp, LinearMap.comp_apply]
  · rw [dif_neg h, dif_neg h]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

/-- **The class of the Eilenberg–Zilber chain of a cycle is `c n` times `(PsiCoef n ρ).hom m`**,
whenever `m` is the trivialised class of `z`.  This is the inverse form of the sign spec
`Work.SSS.PieceInv`, transported through the trivialisation `Work.SSS.triv`. -/
theorem pieceInv_iotaF_class (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSS.PieceAlpha p hfib c)
    (n : ℕ) (ρ : Work.SSS.nIndex (Work.SSS.sSing B) n) (m : Work.SSS.coefM p e₀ t)
    (z : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p
        (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (hm : (ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t
        (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).hom)
        ((Work.SSS.fibreCC p
          (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).homologyπ t
          ((Work.SSS.fibreCC p
            (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz)) = m) :
    (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ)).homologyπ (n+t)
        ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
          (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ)).cyclesMk
          ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) n
            (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))
            (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ) rfl t)) z)
          ((ComplexShape.down ℕ).next (n+t)) rfl
          (Work.SSS.IotaChain.iotaF_cycle p hfib n t
            (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))
            (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ) rfl z hz))
      = c n • ((Work.SSS.PsiCoef p e₀ hfib hc t n ρ).hom m) := by
  have hcyc := Work.SSS.IotaChain.iotaF_cycle p hfib n t
      (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ) rfl z hz
  have hPI := Work.SSS.pieceInv_of_pieceAlpha p hfib c hc1 hal n t
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ) z hz hcyc
  -- the trivialisation sends `m` back to the class of `z`
  have hzh : (ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t
      (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).inv) m
      = (Work.SSS.fibreCC p
          (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).homologyπ t
          ((Work.SSS.fibreCC p
            (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz) := by
    rw [← hm]
    have hcomp := Iso.hom_inv_id (Work.SSS.triv p e₀ hfib hc t
      (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ)))
    have hx := congrArg (fun f => (ConcreteCategory.hom f)
        ((Work.SSS.fibreCC p
          (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).homologyπ t
          ((Work.SSS.fibreCC p
            (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz))) hcomp
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using hx
  have hPsi : (Work.SSS.PsiCoef p e₀ hfib hc t n ρ).hom m
      = (ModuleCat.Hom.hom (Work.SSS.serreE1PieceIso p hfib n t
          (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ)).inv)
          ((Work.SSS.fibreCC p
            (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).homologyπ t
            ((Work.SSS.fibreCC p
              (Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ))).cyclesMk z
              ((ComplexShape.down ℕ).next t) rfl hz)) := by
    simp only [Work.SSS.PsiCoef, Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    rw [hzh]
  have hcc : c n * c n = 1 := by
    rcases hc1 n with h' | h' <;> rw [h'] <;> norm_num
  rw [hPsi, hPI, smul_smul, hcc, one_smul]


/-- `pieceInv_iotaF_class` with the fibre base point `b` kept as an explicit variable
(`hb : sigmaVert (nIndexSigma n ρ) = b`). -/
theorem pieceInv_iotaF_class_b (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSS.PieceAlpha p hfib c)
    (n : ℕ) (ρ : Work.SSS.nIndex (Work.SSS.sSing B) n) (b : B)
    (hb : Work.SSS.sigmaVert (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ) = b)
    (m : Work.SSS.coefM p e₀ t)
    (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
    (hm : (ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t b).hom)
        ((Work.SSS.fibreCC p b).homologyπ t
          ((Work.SSS.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz)) = m) :
    (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ)).homologyπ (n+t)
        ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
          (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ)).cyclesMk
          ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) n b (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ) hb t)) z)
          ((ComplexShape.down ℕ).next (n+t)) rfl
          (Work.SSS.IotaChain.iotaF_cycle p hfib n t b
            (Work.SSS.nIndexSigma (Work.SSS.sSing B) n ρ) hb z hz))
      = c n • ((Work.SSS.PsiCoef p e₀ hfib hc t n ρ).hom m) := by
  subst b
  exact pieceInv_iotaF_class p e₀ hfib hc t c hc1 hal n ρ m z hz hm

/-- Transport of `0` along `pieceCastElem`. -/
lemma pieceCastElem_zero {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m') :
    Work.SSS.pieceCastElem f h (0 : (Work.SSS.pieceAlong f m).X n) = 0 := by
  subst h
  simp only [Work.SSS.pieceCastElem, eqToHom_refl, ModuleCat.id_apply, LinearMap.id_apply]

/-- The face chain `faceB i`, pushed to the graded piece `grF_s`, is a cycle. -/
lemma grFι_faceB_cycle (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1))
    (z : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (i : Fin (s+2)) :
    (ModuleCat.Hom.hom ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t)
        ((ComplexShape.down ℕ).next (s+t))))
      ((ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t))
        (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z i))) = 0 := by
  by_cases hnd : SimplicialObject.δ (Work.SSS.sSing B) i
      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
  · by_cases hi : i = 0
    · subst hi
      have hρ0 : SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ
          = Work.SSS.nIndexSigma (Work.SSS.sSing B) s
              (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                ⟨SimplicialObject.δ (Work.SSS.sSing B) 0
                  (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩) :=
        Work.SSS.nIndexSigma_face σ 0 hnd
      rw [Work.SSS.faceB_grFi_zero p hfib s t σ (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) rfl z _ hρ0]
      rw [Work.SSS.chainMap_comm_apply_elem
        (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
          (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
              ⟨SimplicialObject.δ (Work.SSS.sSing B) 0
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩)) _]
      rw [Work.SSS.d_pieceCastElem]
      simp only [Work.SSS.ezElem]
      rw [Work.SSS.ezLinSnd_chain_cycle p s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)
        (Work.SSS.ezSimplexZero p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
          (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl)
        (by simp) z hz]
      rw [pieceCastElem_zero]
      exact map_zero _
    · have hρi : SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ
          = Work.SSS.nIndexSigma (Work.SSS.sSing B) s
              (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                  (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩) :=
        Work.SSS.nIndexSigma_face σ i hnd
      have h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ)
          = Work.SSS.sigmaVert (Work.SSS.sigHat σ) :=
        Work.SSS.sigmaVert_face i hi (Work.SSS.sigHat σ)
      rw [Work.SSS.faceB_grFi_nondeg p hfib s t σ (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) rfl z
        _ i hi hρi h']
      rw [Work.SSS.chainMap_comm_apply_elem
        (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
          (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
              ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), hnd⟩)) _]
      rw [Work.SSS.d_pieceCastElem]
      simp only [Work.SSS.ezElem]
      rw [Work.SSS.ezLinSnd_chain_cycle p s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
        (SSet.stdSimplex.δ (n := s) i ≫ Work.SSS.sigHat σ)
        (Work.SSS.faceRestr p hfib s (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl i)
        (by
          rw [Work.SSS.faceRestr]
          exact Work.SSS.faceLift_fst (Work.SSS.sSingP p) (Work.SSS.sigHat σ) _ _ i) z hz]
      rw [pieceCastElem_zero]
      exact map_zero _
  · cases s with
    | zero =>
      rw [SSet.nondegenerate_zero] at hnd
      exact absurd (Set.mem_univ _) hnd
    | succ k =>
      rw [Work.SSS.faceB_grFi_degenerate p hfib k t σ z i hnd]
      exact map_zero _


/-- `cyclesMk` of `0` is `0`. -/
lemma cyclesMk_zero {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j)
    (h : (ModuleCat.Hom.hom (K.d i j)) (0 : K.X i) = 0) :
    K.cyclesMk (0 : K.X i) j hj h = 0 := by
  apply (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance
  simp only [map_zero]
  exact HomologicalComplex.i_cyclesMk (K := K) (0 : K.X i) j hj h

/-- The two spellings of the underlying function of a morphism of `ℤ`-modules agree. -/
lemma ccHom {M N : ModuleCat ℤ} (f : M ⟶ N) :
    CategoryTheory.ConcreteCategory.hom f = ModuleCat.Hom.hom f := rfl

/-- The underlying function of a morphism of `ℤ`-modules, through the forgetful functor to `Ab`. -/
lemma ccHomF {M N : ModuleCat ℤ} (f : M ⟶ N) :
    CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map f)
      = ModuleCat.Hom.hom f := rfl

/-- `cyclesMk` is additive: the cycle attached to a linear combination of cycles is the
corresponding linear combination of the cycles attached to the summands (spelled with
`ModuleCat.Hom.hom`). -/
lemma cyclesMk_sum_ {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ} {ι : Type} [Fintype ι]
    (a : ι → ℤ) (x : ι → K.X i)
    (hx : ∀ j, (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) (x j) = 0)
    (h : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) (∑ j, a j • x j) = 0) :
    K.cyclesMk (∑ j, a j • x j) ((ComplexShape.down ℕ).next i) rfl h
      = ∑ j, a j • K.cyclesMk (x j) ((ComplexShape.down ℕ).next i) rfl (hx j) := by
  apply (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance
  simp only [map_sum, map_zsmul, HomologicalComplex.i_cyclesMk]

end Work.SSS

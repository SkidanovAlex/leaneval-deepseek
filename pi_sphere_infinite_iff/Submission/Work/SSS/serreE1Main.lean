import Mathlib
import Submission.Work.SSS.serreE1CruxD1
import Submission.Work.SSS.iotaTLinFace_eq_faceRestr
import Submission.Work.SSS.iotaT_eq_iotaTLin
import Submission.Work.SSS.jF_eq_grFi
import Submission.Work.SSS.faceD_iota
import Submission.Work.SSS.exists_cycleMk
import Submission.Work.SSS.cyclesMk_sum
import Submission.Work.SSS.faceRestr_eq_ezSimplexZero
import Submission.Work.SSS.faceRestr_eq_ezSimplex
import Submission.Work.SSS.d_sndToR_iotaTLin
import Submission.Work.SSS.sndToR_iotaTLinFace
import Submission.Work.SSS.iotaTLin_boundary_explicit
import Submission.Work.SSS.ezSimplexZero_chain_class
import Submission.Work.SSS.d1_eqToHom_conj
import Submission.Work.SSS.nIndexSigma_face
import Submission.Work.SSS.homologyMap_cyclesMk
import Submission.Work.SSS.tensorComplex_d_coef
import Submission.Work.SSS.serreE1Chain
import Submission.Work.SSS.chainCondition_gen
import Submission.Work.SSS.faceB_grFi_nondeg
import Submission.Work.SSS.faceB_grFi_degenerate
import Submission.Work.SSS.faceB_grFi_zero
import Submission.Work.SSS.iotaF_pieceCastElem
import Submission.Work.SSS.kF_psiCoef_gen
import Submission.Work.SSS.mapPhiY_iotaF_gen

/-!
# The chain condition for `PsiG`: assembly

This file assembles `Work.SSS.serreE1` from the generator-level computation
`Work.SSS.chainCondition_gen` (the elementwise description of `d¹` on the generators `[σ] ⊗ m`,
whose inputs are `Work.SSS.kF_psiCoef_gen`, `Work.SSS.faceB_grFi_*`, `Work.SSS.iotaF_pieceCastElem`,
`Work.SSS.ezSimplexZero_chain_class`, `Work.SSS.d_sndToR_iotaTLin`,
`Work.SSS.mapPhiY_iotaF_gen`, `Work.SSS.jF_eq_grFi`, `Work.SSS.faceD_iota` and
`Work.SSS.tensorComplex_d_coef`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]


/-- **The chain condition for `PsiSig`**, up to a dimension-dependent sign. -/
theorem PsiSig_chainCondition (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) :
    ∃ eps : ℕ → ℤ, (∀ s : ℕ, eps s = 1 ∨ eps s = -1) ∧
      ∀ s : ℕ, Work.SSS.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSS.d1 (Work.SSS.xiCan p) s t
        = eps s • (Work.SSS.faceD' (Work.SSS.sSing B) (Work.SSS.coefM p e₀ t) s ≫
            Work.SSS.PsiSig p e₀ hfib hc t s) := by
  obtain ⟨c, hc1, hal⟩ := exists_pieceAlpha p hfib
  refine ⟨fun s => c (s+1) * c s, ?_, ?_⟩
  · intro s
    show c (s+1) * c s = 1 ∨ c (s+1) * c s = -1
    rcases hc1 (s+1) with h | h <;> rcases hc1 s with h' | h' <;> rw [h, h'] <;> norm_num
  · intro s
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    ext m
    have hinv : (Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
        ((Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).inv.hom m) = m := by
      have h := Iso.inv_hom_id (Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)))
      have hx := congrArg (fun (f : Work.SSS.coefM p e₀ t ⟶ Work.SSS.coefM p e₀ t) =>
        (ModuleCat.Hom.hom f) m) h
      simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using hx
    rw [← hinv]
    obtain ⟨z, hz, hzy⟩ := exists_cycleMk
      (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))) t
      ((Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).inv.hom m)
    rw [hzy]
    exact chainCondition_gen p e₀ hfib hc t c hc1 hal s σ z hz

end

end Work.SSS

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex

noncomputable section

/-- **The chain condition for `PsiG` in the general `(ξ, hξ)` form.** -/
theorem serreE1_chainCondition {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) :
    ∃ eps : ℕ → ℤ, (∀ s : ℕ, eps s = 1 ∨ eps s = -1) ∧
      ∀ (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
        (hξ : ξ.F = Fc p) (s : ℕ),
        PsiG p e₀ hfib hc t ξ hξ (s+1) ≫ d1 ξ s t
          = eps s • ((tensorComplex (Nn B) (coefM p e₀ t)).d (s+1) s ≫
              PsiG p e₀ hfib hc t ξ hξ s) := by
  obtain ⟨eps, heps, hcan⟩ := PsiSig_chainCondition p e₀ hfib hc t
  refine ⟨eps, heps, ?_⟩
  intro ξ hξ s
  have hconj : (eqToHom (congrArg (fun F => (grF F (s+1)).homology ((s+1)+t)) hξ.symm) ≫
      d1 ξ s t) = d1 (xiCan p) s t ≫
      eqToHom (congrArg (fun F => (grF F s).homology (s+t)) hξ.symm) :=
    d1_eqToHom_conj (xiCan p) ξ hξ.symm s t
  have hcoef : ((tensorComplex (Nn B) (coefM p e₀ t)).d (s+1) s ≫
      (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) s).inv)
      = (serreE1CoefIsoIso (sSing B) (coefM p e₀ t) (s+1)).inv ≫
        faceD' (sSing B) (coefM p e₀ t) s := by
    rw [← tensorComplex_d_coef (sSing B) (coefM p e₀ t) s, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [PsiG_eq, PsiG_eq]
  simp only [Category.assoc]
  rw [hconj]
  rw [show (PsiSig p e₀ hfib hc t (s+1) ≫ d1 (xiCan p) s t ≫
        eqToHom (congrArg (fun F => (grF F s).homology (s+t)) hξ.symm))
      = ((PsiSig p e₀ hfib hc t (s+1) ≫ d1 (xiCan p) s t) ≫
        eqToHom (congrArg (fun F => (grF F s).homology (s+t)) hξ.symm)) from
      (Category.assoc _ _ _).symm]
  rw [hcan]
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  conv_lhs => rw [Category.assoc, ← Category.assoc, ← hcoef, Category.assoc]

end

end Work.SSS

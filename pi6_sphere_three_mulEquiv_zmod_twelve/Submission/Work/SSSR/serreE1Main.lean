import Mathlib
import Submission.Work.SSSR.serreE1CruxD1
import Submission.Work.SSSR.iotaTLinFace_eq_faceRestr
import Submission.Work.SSSR.iotaT_eq_iotaTLin
import Submission.Work.SSSR.jF_eq_grFi
import Submission.Work.SSSR.faceD_iota
import Submission.Work.SSSR.exists_cycleMk
import Submission.Work.SSSR.cyclesMk_sum
import Submission.Work.SSSR.faceRestr_eq_ezSimplexZero
import Submission.Work.SSSR.faceRestr_eq_ezSimplex
import Submission.Work.SSSR.d_sndToR_iotaTLin
import Submission.Work.SSSR.sndToR_iotaTLinFace
import Submission.Work.SSSR.iotaTLin_boundary_explicit
import Submission.Work.SSSR.ezSimplexZero_chain_class
import Submission.Work.SSSR.d1_eqToHom_conj
import Submission.Work.SSSR.nIndexSigma_face
import Submission.Work.SSSR.homologyMap_cyclesMk
import Submission.Work.SSSR.tensorComplex_d_coef
import Submission.Work.SSSR.serreE1Chain
import Submission.Work.SSSR.chainCondition_gen
import Submission.Work.SSSR.faceB_grFi_nondeg
import Submission.Work.SSSR.faceB_grFi_degenerate
import Submission.Work.SSSR.faceB_grFi_zero
import Submission.Work.SSSR.iotaF_pieceCastElem
import Submission.Work.SSSR.kF_psiCoef_gen
import Submission.Work.SSSR.mapPhiY_iotaF_gen
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex
noncomputable section

attribute [local instance] Classical.propDecidable

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]


/-- **The chain condition for `PsiSig`**, up to a dimension-dependent sign. -/
theorem PsiSig_chainCondition (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) :
    ∃ eps : ℕ → ℤ, (∀ s : ℕ, eps s = 1 ∨ eps s = -1) ∧
      ∀ s : ℕ, Work.SSSR.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSSR.d1 (Work.SSSR.xiCan (R := R) p) s t
        = eps s • (Work.SSSR.faceD' (Work.SSSR.sSing B) (Work.SSSR.coefM p e₀ t) s ≫
            Work.SSSR.PsiSig p e₀ hfib hc t s) := by
  obtain ⟨c, hc1, hal⟩ := exists_pieceAlpha (R := R) p hfib
  refine ⟨fun s => c (s+1) * c s, ?_, ?_⟩
  · intro s
    show c (s+1) * c s = 1 ∨ c (s+1) * c s = -1
    rcases hc1 (s+1) with h | h <;> rcases hc1 s with h' | h' <;> rw [h, h'] <;> norm_num
  · intro s
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    ext m
    have hinv : (Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
        ((Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).inv.hom m) = m := by
      have h := Iso.inv_hom_id (Work.SSSR.triv (R := R) p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)))
      have hx := congrArg (fun (f : Work.SSSR.coefM p e₀ t ⟶ Work.SSSR.coefM p e₀ t) =>
        (ModuleCat.Hom.hom f) m) h
      simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using hx
    rw [← hinv]
    obtain ⟨z, hz, hzy⟩ := exists_cycleMk
      (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))) t
      ((Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).inv.hom m)
    rw [hzy]
    exact chainCondition_gen p e₀ hfib hc t c hc1 hal s σ z hz

end

end Work.SSSR

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex
noncomputable section

/-- **The chain condition for `PsiG` in the general `(ξ, hξ)` form.** -/
theorem serreE1_chainCondition {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) :
    ∃ eps : ℕ → ℤ, (∀ s : ℕ, eps s = 1 ∨ eps s = -1) ∧
      ∀ (ξ : Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)))
        (hξ : ξ.F = Fc p) (s : ℕ),
        PsiG p e₀ hfib hc t ξ hξ (s+1) ≫ d1 ξ s t
          = eps s • ((tensorComplex R (Nn B) (coefM p e₀ t)).d (s+1) s ≫
              PsiG p e₀ hfib hc t ξ hξ s) := by
  obtain ⟨eps, heps, hcan⟩ := PsiSig_chainCondition (R := R) p e₀ hfib hc t
  refine ⟨eps, heps, ?_⟩
  intro ξ hξ s
  have hconj : (eqToHom (congrArg (fun F => (grF F (s+1)).homology ((s+1)+t)) hξ.symm) ≫
      d1 ξ s t) = d1 (xiCan p) s t ≫
      eqToHom (congrArg (fun F => (grF F s).homology (s+t)) hξ.symm) :=
    d1_eqToHom_conj (xiCan p) ξ hξ.symm s t
  have hcoef : ((tensorComplex R (Nn B) (coefM p e₀ t)).d (s+1) s ≫
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

end Work.SSSR

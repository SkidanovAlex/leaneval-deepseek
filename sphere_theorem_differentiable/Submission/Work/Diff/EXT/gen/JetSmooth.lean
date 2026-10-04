import Mathlib
import Submission.Work.Diff.EXT.gen.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the jet/sequence machinery (generic, local form)

`Submission/Work/Diff/EXT/contDiff_sJet_tderiv.lean` and `.../contDiff_Aseq_Psi.lean` prove, for
`ℝ × ℝⁿ → ℝᵐ` and globally smooth data, that `sJet`, `tderiv`, `Aseq`, `Seq`, `Psi` of smooth data
are smooth.  This file proves the corresponding statements for arbitrary real normed spaces `E`, `F`
and for data that are only smooth on an open set `V`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT.gen

open Work.Diff.EXT (sJetG tderivG AseqG SeqG PsiG JG)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuous linear map `T ↦ T.comp (inr ℝ ℝ E)`. -/
noncomputable def compInrCLM : ((ℝ × E) →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) (ContinuousLinearMap.inr ℝ ℝ E)).comp
    (ContinuousLinearMap.compL ℝ E (ℝ × E) F)

theorem compInrCLM_apply (T : (ℝ × E) →L[ℝ] F) :
    compInrCLM (E := E) (F := F) T = T.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  simp [compInrCLM, ContinuousLinearMap.compL_apply, ContinuousLinearMap.apply_apply]

/-- The spatial derivative (as a function of the base point) of a function that is smooth on an
open set is smooth on that set. -/
theorem contDiffOn_slice_fderiv {V : Set (ℝ × E)} (hV : IsOpen V) {g : ℝ × E → F}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × E => fderiv ℝ (fun y : E => g (z.1, y)) z.2) V := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ g) V := hg.fderiv_of_isOpen hV (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)
  have hCLM : ContDiff ℝ (⊤ : ℕ∞) (compInrCLM (E := E) (F := F)) :=
    ContinuousLinearMap.contDiff (compInrCLM (E := E) (F := F))
  have hcomp' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × E => compInrCLM (E := E) (F := F) (fderiv ℝ g z)) V :=
    hCLM.comp_contDiffOn hd
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × E => (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ ℝ E)) V :=
    hcomp'.congr (fun z _ => compInrCLM_apply (F := F) (fderiv ℝ g z))
  exact hcomp.congr (fun z hz => Work.Diff.EXT.fderiv_comp_inr_aux
    ((hg.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)))

/-- The time derivative of a function that is smooth on an open set is smooth on that set. -/
theorem contDiffOn_slice_tderiv {V : Set (ℝ × E)} (hV : IsOpen V) {g : ℝ × E → F}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) : ContDiffOn ℝ (⊤ : ℕ∞) (tderivG g) V := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ g) V := hg.fderiv_of_isOpen hV (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)
  have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × E => (fderiv ℝ g z) (1, 0)) V :=
    hd.clm_apply contDiffOn_const
  refine h.congr (fun z hz => ?_)
  rw [tderivG_apply]
  exact (Work.Diff.EXT.jets_eq_fderiv_fst_apply g
    ((hg.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp))).symm

/-- The spatial `2`-jet of a function that is smooth on an open set is smooth on that set. -/
theorem contDiffOn_sJetG {V : Set (ℝ × E)} (hV : IsOpen V) {g : ℝ × E → F}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) : ContDiffOn ℝ (⊤ : ℕ∞) (sJetG g) V := by
  have h2 := contDiffOn_slice_fderiv hV hg
  have h3 := contDiffOn_slice_fderiv hV h2
  refine (hg.prodMk (h2.prodMk h3)).congr (fun z hz => ?_)
  rfl

/-- **Smoothness of the jet/sequence machinery on an open set.** -/
theorem contDiffOn_jet_sequence {V : Set (ℝ × E)} (hV : IsOpen V)
    (Φ : E × JG E F → F) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {a : ℝ × E → F}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a V) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sJetG a) V ∧ ContDiffOn ℝ (⊤ : ℕ∞) (tderivG a) V ∧
    (∀ j : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (AseqG Φ a j) V) ∧
    (∀ i : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (SeqG Φ a i) V) ∧
    (∀ i : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (sJetG (SeqG Φ a i)) V) ∧
    (∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (PsiG Φ j)) ∧
    (∀ j : ℕ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × E => PsiG Φ j (z.2, fun i : Fin (j + 1) => sJetG (SeqG Φ a i) z)) V) := by
  have hsJet : ContDiffOn ℝ (⊤ : ℕ∞) (sJetG a) V := contDiffOn_sJetG hV ha
  have hA : ∀ j : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (AseqG Φ a j) V := by
    intro j
    induction j with
    | zero =>
      rw [AseqG_zero]
      refine (ContDiff.comp_contDiffOn hΦ (contDiffOn_snd.prodMk hsJet)).congr (fun z hz => ?_)
      rfl
    | succ j ih =>
      rw [AseqG_succ]
      exact contDiffOn_slice_tderiv hV ih
  have hSeq : ∀ i : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (SeqG Φ a i) V := by
    intro i
    cases i with
    | zero => rw [SeqG_zero]; exact ha
    | succ j => rw [SeqG_succ]; exact hA j
  have hsJetSeq : ∀ i : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (sJetG (SeqG Φ a i)) V :=
    fun i => contDiffOn_sJetG hV (hSeq i)
  have hPsi : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (PsiG Φ j) := by
    intro j
    induction j with
    | zero =>
      have h : PsiG Φ 0 = fun p : E × (Fin 1 → JG E F) => Φ (p.1, p.2 0) := rfl
      rw [h]
      exact hΦ.comp (contDiff_fst.prodMk
        ((contDiff_apply ℝ (JG E F) (0 : Fin 1)).comp contDiff_snd))
    | succ j ih =>
      have h : PsiG Φ (j + 1) = fun p : E × (Fin (j + 2) → JG E F) =>
          ∑ i : Fin (j + 1),
            (fderiv ℝ (fun q : E × (Fin (j + 1) → JG E F) => PsiG Φ j q)
              (p.1, fun k => p.2 k.castSucc)) (0, Pi.single i (p.2 i.succ)) := rfl
      rw [h]
      refine ContDiff.sum (fun i _ => ?_)
      have hfd : ContDiff ℝ (⊤ : ℕ∞)
          (fun x : E × (Fin (j + 2) → JG E F) =>
            fderiv ℝ (fun q : E × (Fin (j + 1) → JG E F) => PsiG Φ j q)
              (x.1, fun k : Fin (j + 1) => x.2 k.castSucc)) := by
        have hun : ContDiff ℝ (⊤ : ℕ∞)
            (Function.uncurry (fun (_ : E × (Fin (j + 2) → JG E F))
                (q : E × (Fin (j + 1) → JG E F)) => PsiG Φ j q)) := by
          rw [show Function.uncurry (fun (_ : E × (Fin (j + 2) → JG E F))
                (q : E × (Fin (j + 1) → JG E F)) => PsiG Φ j q)
                = (fun r : (E × (Fin (j + 2) → JG E F)) × (E × (Fin (j + 1) → JG E F)) =>
                    PsiG Φ j r.2) from rfl]
          exact ih.comp contDiff_snd
        have hφ : ContDiff ℝ (⊤ : ℕ∞)
            (fun x : E × (Fin (j + 2) → JG E F) =>
              ((x.1, fun k : Fin (j + 1) => x.2 k.castSucc) :
                E × (Fin (j + 1) → JG E F))) :=
          contDiff_fst.prodMk
            (contDiff_pi.mpr
              (fun k => (contDiff_apply ℝ (JG E F) k.castSucc).comp contDiff_snd))
        exact ContDiff.fderiv hun hφ (by simp)
      refine ContDiff.clm_apply hfd ?_
      refine contDiff_const.prodMk ?_
      exact (ContinuousLinearMap.contDiff
        (ContinuousLinearMap.single ℝ (fun _ : Fin (j + 1) => JG E F) i)).comp
          ((contDiff_apply ℝ (JG E F) i.succ).comp contDiff_snd)
  have hPsiComp : ∀ j : ℕ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × E => PsiG Φ j (z.2, fun i : Fin (j + 1) => sJetG (SeqG Φ a i) z)) V := by
    intro j
    refine (ContDiff.comp_contDiffOn (hPsi j)
      (contDiffOn_snd.prodMk (contDiffOn_pi.mpr (fun i => hsJetSeq i)))).congr
      (fun z hz => ?_)
    rfl
  exact ⟨hsJet, contDiffOn_slice_tderiv hV ha, hA, hSeq, hsJetSeq, hPsi, hPsiComp⟩

end Work.Diff.EXT.gen

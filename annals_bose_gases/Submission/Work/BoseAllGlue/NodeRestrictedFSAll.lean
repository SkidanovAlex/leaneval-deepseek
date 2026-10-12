import ChallengeDeps
import Submission.Work.BoseAllGlue.AllAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.nodeRestrictedB_of_residualsFSAll` — the final glue, `All` vocabulary

Design item 5 glue (D3), row 4: the `All`-vocabulary port of
`Work.BoseFixR.nodeRestrictedB_of_residualsFS` (`BoseFixR/NodeRestrictedBFS.lean`).

The frozen node `Work.BoseBoxFix.NodeRestrictedB v h J' η₀ C` follows from the four `All`
residuals

* `RB4boxDomAtAll v h R J' fc fu HM` — FS §8 at the model, with `valFSAll`;
* the `All` view `(HonestBoxFam … μ).viewFSAll v h μ` on the diluteness ball `{μa³ ≤ ε}`;
* `RB5FSAll v h R (HonestBoxFam …)` — FS §9 (far region), i.e. the bound on the
  `KzOpFSAll`-form;
* `RB67FSAll v h R (HonestBoxFam …)` — FS §10+§11 (close region);

together with `NodeB1B` (`eq:apriorinn+`), whose first conjunct gives the `n ≤ 2μℓ³`
requirement of `RB4boxDomAtAll` (via
`Work.BoseFixB2.DvApriori.exists_window_factor_le`).

The port is the original's proof with `valFS → valFSAll` and, correspondingly,
`KzValFS_le_of_bound → Work.BoseAllGlue.valFSAll_ge_of_bound`; every other ingredient
(`AbsorbFar`, `AbsorbCloseFix`, `bigK`, `closeCondFS_lower`, `farCondFS_of_not_close`,
`honestBoxFam_window`, `adm_mono`, `ell3`, `Lambda`, `errKafz`, `BoxBoundB`, the degenerate
`normB = 0` case) is operator-free or already at `KzOpFSAll`-independent scalars and is reused
verbatim.

The statement is copied from `Submission/Work/BOSE_ALL_STATEMENTS.lean.txt` (item 5 glue).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFock
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-- **`NodeRestrictedB` from the corrected `All` residuals at the honest model.** -/
theorem nodeRestrictedB_of_residualsFSAll {v : ℝ³ → ℝ} {h : ScatSol v} {R J' : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hR : 0 ≤ R) (hJ' : Work.UBB.lhyC < J') (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (hB1 : Work.BoseBoxFix.NodeB1B v h J')
    (hdom : Work.BoseBoxFock.RB4boxDomAtAll v h R J' fc fu HM) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hview : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (h5 : Work.BoseBoxFock.RB5FSAll v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM))
    (h67 : Work.BoseBoxFock.RB67FSAll v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM)) :
    ∃ η₀ : ℝ, 1 / 2000 < η₀ ∧ η₀ < 2 / 323 ∧ ∃ C : ℝ, 0 ≤ C ∧ Work.BoseBoxFix.NodeRestrictedB v h J' η₀ C := by
  obtain ⟨εd, Cd, hεd, hCd, hred⟩ := hdom
  obtain ⟨ε₅, hε₅, hfar⟩ := h5
  obtain ⟨ε₆, C₆, hε₆, hC₆, hclose⟩ := h67
  obtain ⟨C₁, C₂, εB1, hC₁, hC₂, hεB1, hB1'⟩ := hB1
  obtain ⟨εw, hεw, hwf⟩ := Work.BoseFixB2.DvApriori.exists_window_factor_le v hav hC₁
  refine ⟨1 / 1800, by norm_num, by norm_num, bigK (a v) R Cd C₆,
    bigK_nonneg hav hR hCd hC₆, ?_⟩
  refine ⟨min (min εd ε₅) (min ε₆ (min 1 (min (min εB1 εw) ε))), ?_, ?_⟩
  · refine lt_min (lt_min hεd hε₅) (lt_min hε₆ (lt_min one_pos (lt_min (lt_min hεB1 hεw) hε)))
  intro μ hAdm hJKB n Φ hlow hspec
  -- ## the threshold bookkeeping
  have hε₀d : min (min εd ε₅) (min ε₆ (min 1 (min (min εB1 εw) ε))) ≤ εd :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₀₅ : min (min εd ε₅) (min ε₆ (min 1 (min (min εB1 εw) ε))) ≤ ε₅ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₀₆ : min (min εd ε₅) (min ε₆ (min 1 (min (min εB1 εw) ε))) ≤ ε₆ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀1 : min (min εd ε₅) (min ε₆ (min 1 (min (min εB1 εw) ε))) ≤ 1 :=
    le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₀B1 : min (min εd ε₅) (min ε₆ (min 1 (min (min εB1 εw) ε))) ≤ εB1 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hε₀w : min (min εd ε₅) (min ε₆ (min 1 (min (min εB1 εw) ε))) ≤ εw :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hε₀ε : min (min εd ε₅) (min ε₆ (min 1 (min (min εB1 εw) ε))) ≤ ε :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hAdmd : Adm v εd μ := adm_mono hε₀d hAdm
  have hAdm₅ : Adm v ε₅ μ := adm_mono hε₀₅ hAdm
  have hAdm₆ : Adm v ε₆ μ := adm_mono hε₀₆ hAdm
  have hAdmB1 : Adm v εB1 μ := adm_mono hε₀B1 hAdm
  have hμ : 0 < μ := adm_pos hAdmd
  have hdilpos : 0 < dil v μ := by rw [dil]; positivity
  have hdil1 : dil v μ ≤ 1 := le_trans (adm_dil hAdm) hε₀1
  have hdilε : dil v μ ≤ ε := le_trans (adm_dil hAdm) hε₀ε
  have hdilw : dil v μ ≤ εw := le_trans (adm_dil hAdm) hε₀w
  have hℓ : 0 < ell v μ := ell_pos' v hμ hav
  have hv := hview μ hμ hdilε
  have hwin := honestBoxFam_window (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM) μ hμ hav
  have hne : Nonempty {f : (HonestBoxFam v h fc fu HM μ).F.H //
      (HonestBoxFam v h fc fu HM μ).T.NWindow (HonestBoxFam v h fc fu HM μ).E.bigM f
        ∧ f ≠ 0} := by
    obtain ⟨f₀, h1, h2⟩ := hwin
    exact ⟨⟨f₀, h1, h2⟩⟩
  rcases lt_or_eq_of_le (normB_nonneg v μ n Φ) with hpos | hzero
  swap
  · -- ## degenerate case: the state vanishes on the box
    rw [BoxBoundB]
    have hℓ' : 0 < sideAt μ (a v) := hℓ
    have h0 : ∀ x ∈ abox n (sideAt μ (a v)), (Φ : X n → ℝ) x = 0 :=
      Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero (ℓ := sideAt μ (a v)) hℓ'
        Φ.contDiff.continuous
        (by simpa [Work.BoseBoxFix.normB] using hzero.symm)
    have hword : wordB v h μ n Φ = 0 := by
      rw [Work.BoseBoxFix.wordB]
      exact Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox hℓ' h0
    rw [hword, ← hzero]
    simp  -- ## the main case
  -- `n ≤ 2μℓ³` from `NodeB1B`'s first conjunct
  have hn2 : (n : ℝ) ≤ 2 * μ * sideAt μ (a v) ^ 3 := by
    obtain ⟨hwin1, -⟩ := hB1' μ hAdmB1 hJKB n Φ hpos hlow
    -- `C₁ · nWindow ≤ μℓ³/2`
    have hfac : C₁ * ((paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (paramsAt μ (a v)).Kl
        * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ)) ≤ 1 / 2 := hwf μ hμ hdilw
    have hC₁nw : C₁ * Work.BoseBox.nWindow (paramsAt μ (a v)) μ (a v)
        ≤ (1 / 2) * (μ * sideAt μ (a v) ^ 3) := by
      calc C₁ * Work.BoseBox.nWindow (paramsAt μ (a v)) μ (a v)
          = C₁ * (μ * sideAt μ (a v) ^ 3
              * ((paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (paramsAt μ (a v)).Kl
                  * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ))) := by
            rw [Work.BoseFixB1.nWindow_eq]; ring
        _ = μ * sideAt μ (a v) ^ 3 * (C₁ * ((paramsAt μ (a v)).KB ^ (3 / 2 : ℝ)
              * (paramsAt μ (a v)).Kl * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ))) := by ring
        _ ≤ μ * sideAt μ (a v) ^ 3 * (1 / 2) :=
            mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = (1 / 2) * (μ * sideAt μ (a v) ^ 3) := by ring
    have habs := abs_le.mp hwin1
    nlinarith [habs.2, hC₁nw]
  -- ## the §11 absorption, for every ρ ≥ 0
  have hpoint : ∀ ρ : {ρ : ℝ // 0 ≤ ρ},
      (ell3 v μ * Lambda (a v) (bigK (a v) R Cd C₆) (1 / 1800) μ
          + errKafz v R μ Cd) * normB v μ n Φ
        ≤ (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1 * normB v μ n Φ := by
    intro ρ
    have hN := normB_nonneg v μ n Φ
    by_cases hc : Work.BoseBoxFock.CloseCondFS v μ ρ.1
    · have hCb : CloseBoundR v R μ C₆ ρ.1 ≤ (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1 :=
        Work.BoseAllGlue.valFSAll_ge_of_bound (HonestBoxFam v h fc fu HM μ) hne
          (fun f hf hfne => hclose μ hAdm₆ hv ρ.1 ρ.2 hc f hf)
      have hAbs := AbsorbClose (a := a v) (ℓ := ell v μ) (t := dil v μ) (μ := μ) (R := R)
        (C₄ := Cd) (C₆ := C₆) (K := bigK (a v) R Cd C₆) (η₀ := 1 / 1800) (ρ := ρ.1)
        hav hℓ hμ hR hCd hC₆ (by norm_num) (by norm_num) (by norm_num) hdilpos hdil1 le_rfl ρ.2
        (le_of_eq (by rw [dil])) (closeCondFS_lower hμ hav hc)
      rw [← errKafz_eq_errAbs v hμ hav, ← Lambda_ell3' v,
        ← fsX_sq v hμ hav, ← errExp_eq] at hAbs
      exact mul_le_mul_of_nonneg_right (le_trans hAbs hCb) hN
    · have hfc : Work.BoseBoxFock.FarCondFS v μ ρ.1 := farCondFS_of_not_close hc
      have hFb : FarBound v μ ≤ (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1 :=
        Work.BoseAllGlue.valFSAll_ge_of_bound (HonestBoxFam v h fc fu HM μ) hne
          (fun f hf hfne => hfar μ hAdm₅ hv ρ.1 ρ.2 hfc f hf)
      have hAbs := AbsorbFar (a := a v) (ℓ := ell v μ) (t := dil v μ) (μ := μ) (R := R)
        (C₄ := Cd) (C₆ := C₆) (K := bigK (a v) R Cd C₆) (η₀ := 1 / 1800)
        hav hℓ hμ hR hCd hC₆ (by norm_num) (by norm_num) (by norm_num) hdilpos hdil1 le_rfl
      rw [← errKafz_eq_errAbs v hμ hav, ← Lambda_ell3', ← FarBound_eq' v μ] at hAbs
      exact mul_le_mul_of_nonneg_right (le_trans hAbs hFb) hN
  have hci : (ell3 v μ * Lambda (a v) (bigK (a v) R Cd C₆) (1 / 1800) μ
        + errKafz v R μ Cd) * normB v μ n Φ
      ≤ ⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}),
          (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1 * normB v μ n Φ := by
    haveI := nonemptyDensity
    exact le_ciInf (fun ρ => hpoint ρ)
  have hbridge := hred μ hAdmd hJKB n Φ hn2 hlow hspec
  have hmain : (ell3 v μ * Lambda (a v) (bigK (a v) R Cd C₆) (1 / 1800) μ) * normB v μ n Φ
      ≤ wordB v h μ n Φ := by
    have h1 : (ell3 v μ * Lambda (a v) (bigK (a v) R Cd C₆) (1 / 1800) μ) * normB v μ n Φ
        + errKafz v R μ Cd * normB v μ n Φ
        ≤ wordB v h μ n Φ + errKafz v R μ Cd * normB v μ n Φ := by
      calc (ell3 v μ * Lambda (a v) (bigK (a v) R Cd C₆) (1 / 1800) μ) * normB v μ n Φ
            + errKafz v R μ Cd * normB v μ n Φ
          = (ell3 v μ * Lambda (a v) (bigK (a v) R Cd C₆) (1 / 1800) μ
              + errKafz v R μ Cd) * normB v μ n Φ := by ring
        _ ≤ ⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}),
              (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1 * normB v μ n Φ := hci
        _ ≤ wordB v h μ n Φ + errKafz v R μ Cd * normB v μ n Φ := hbridge
    linarith
  rw [BoxBoundB]
  exact hmain

/-- **The same node, with the far leg's actual deliverable `RB5FSAllK` as its input.**  The far
leg (`BoseFixR`) produces `RB5FSAllK` (the same statement with the conclusion still at
`KzOpFS`), and `Work.BoseBoxFock.RB5FSAll_of_K` converts it to `RB5FSAll` at the price of the
label-`0` coefficient being nonnegative (which the gate supplies).  This wrapper spares the
caller the conversion. -/
theorem nodeRestrictedB_of_residualsFSAllK {v : ℝ³ → ℝ} {h : ScatSol v} {R J' : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hR : 0 ≤ R) (hJ' : Work.UBB.lhyC < J') (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (hB1 : Work.BoseBoxFix.NodeB1B v h J')
    (hdom : Work.BoseBoxFock.RB4boxDomAtAll v h R J' fc fu HM) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hview : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (h5K : Work.BoseBoxFock.RB5FSAllK v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM))
    (h67 : Work.BoseBoxFock.RB67FSAll v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM)) :
    ∃ η₀ : ℝ, 1 / 2000 < η₀ ∧ η₀ < 2 / 323 ∧ ∃ C : ℝ, 0 ≤ C ∧ Work.BoseBoxFix.NodeRestrictedB v h J' η₀ C :=
  nodeRestrictedB_of_residualsFSAll hav hR hJ' fc fu HM hB1 hdom hε hε1 hview
    (Work.BoseBoxFock.RB5FSAll_of_K hav h5K) h67

end Work.BoseFixR

namespace Work.BoseAllGlue

/-- The `Work.BoseAllGlue` name of `Work.BoseFixR.nodeRestrictedB_of_residualsFSAll`. -/
alias nodeRestrictedB_of_residualsFSAll := Work.BoseFixR.nodeRestrictedB_of_residualsFSAll

/-- The `Work.BoseAllGlue` name of `Work.BoseFixR.nodeRestrictedB_of_residualsFSAllK`. -/
alias nodeRestrictedB_of_residualsFSAllK := Work.BoseFixR.nodeRestrictedB_of_residualsFSAllK

end Work.BoseAllGlue

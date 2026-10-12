import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseFixB2.DvApriori.exists_window_factor_le
import Submission.Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox
import Submission.Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/NodeRestrictedBFS.lean` — the final glue, FS vocabulary

The lead's interface change (`BOSE_BOXFOCK_LEAD.md`) replaces the residuals of
`Defs.lean` by the corrected ones `Work.BoseBoxFock.RB4boxDomAt`, `RB5FS`,
`RB67FS` at the **concrete honest model** `HonestBoxFam v h fc fu HM` (FS's
lattice cube `Lab N = Fin 3 → ZMod (2N+1)` with the symmetric representative, the
box mode system `boxFockData corpusBox`, the corrected `TildeData` with
`NH` on the χ-modes, FS's smoothed kinetic symbol `tauSm`, the cut-off `Ŵ₁` and
the corrected `χ̂` normalisation) and the corrected operator `KzOpFS`.

This module proves the **glue**: the frozen node
`Work.BoseBoxFix.NodeRestrictedB v h J' η₀ C` from

* `RB4boxDomAt v h R J' fc fu HM` — FS §8 at that model (with the `n ≤ 2μℓ³`
  restriction on the box states);
* the view `(HonestBoxFam … μ).viewFS v h μ` on the diluteness ball `{μa³ ≤ ε}`;
* `RB5FS v h R (HonestBoxFam …)` — FS §9 (far region);
* `RB67FS v h R (HonestBoxFam …)` — FS §10+§11 (close region);

together with `NodeB1B` (`eq:apriorinn+`), whose first conjunct gives the
`n ≤ 2μℓ³` requirement of `RB4boxDomAt` (via
`Work.BoseFixB2.DvApriori.exists_window_factor_le`: the window factor
`K_B^{3/2}K_ℓ(μa³)^{1/4} = (μa³)^{281/1292}` is small at small diluteness).

The proof is the port of the proved lemmas of this directory to the corrected
vocabulary:

* `KzValFS_le_of_bound` — the `KzVal_le_of_bound` API for `KzValFS`
  (`Defs.lean`);
* `honestBoxFam_window` — the nonzero `𝓜`-window state, from the Fock vacuum
  (`HonestVacuum.vac_killed` + `TildeData.window_nonempty_of_vac`);
* `Assembly.nodeRestrictedB_of_residuals`'s §11 absorption verbatim
  (`AbsorbFar`, `AbsorbCloseFix`, `bigK`), with `(D μ).valFS` in place of
  `(D μ).val`;
* the degenerate case `normB = 0` (`Work.BoseFixGlue.Ports.LHYBoxB_of_grading`'s
  argument: such a state vanishes on the box, hence `wordB = 0`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFock
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The `KzValFS` API -/

/-- `KzValFS_le_of_bound`: a lower bound valid for every (nonzero) window state
bounds `KzValFS` — the port of `Defs.lean`'s `KzVal_le_of_bound`. -/
lemma KzValFS_le_of_bound {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ)
    (hne : Nonempty {f : F.H // T.NWindow E.bigM f ∧ f ≠ 0}) {B : ℝ}
    (h : ∀ f : F.H, T.NWindow E.bigM f → f ≠ 0 →
      B * F.normSq f ≤ F.qw f (KzOpFS F T E gHat0 ρ)) :
    B ≤ KzValFS F T E gHat0 ρ := by
  letI := hne
  refine le_ciInf fun f => ?_
  rw [le_div_iff₀ (normSq_pos F f.2.2)]
  exact h f.1 f.2.1 f.2.2

/-! ## 2. The nonzero window state at the honest family -/

/-- The honest `T.N` is `totNumOp m` (`BoseBoxFock.tildeDataHon`), whose kernel
contains the Fock vacuum, so the `𝓜`-window is inhabited at every `𝓜 ≥ 0`
(`TildeData.window_nonempty_of_vac`). -/
lemma honestBoxFam_window {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} (μ : ℝ) (hμ : 0 < μ) (hav : 0 < a v) :
    ∃ f₀ : (HonestBoxFam v h fc fu HM μ).F.H,
      (HonestBoxFam v h fc fu HM μ).T.NWindow (HonestBoxFam v h fc fu HM μ).E.bigM f₀
        ∧ f₀ ≠ 0 := by
  have hM : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.bigM := by
    show 0 ≤ bigM (paramsAt μ (a v)) (a v) μ
    exact (Work.BoseBox.bigM_pos_of_params hμ hav).le
  refine Work.BoseB7A.TildeData.window_nonempty_of_vac _ hM ?_
  obtain ⟨f₀, hne, hkill⟩ := vac_killed (HM μ).m
  exact ⟨f₀, hne, hkill⟩

/-! ## 3. The node -/

/-! ## 3. The `CloseCondFS` threshold arithmetic -/

/-- `CloseCondFS v μ ρ` (FS `eq:Close` at the corrected threshold
`μK_ℓ^{-2}/(2¹⁴π)`) bounds `ρ` from below by `μ(1 − (μa³)^{3/323})`, the form
`AbsorbClose` consumes (`K_ℓ^{-2} = (μa³)^{3/323}`, `Arith.Kl_inv_sq`). -/
lemma closeCondFS_lower {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ} (hμ : 0 < μ)
    (hav : 0 < a v) (hc : Work.BoseBoxFock.CloseCondFS v μ ρ) :
    μ * (1 - (dil v μ) ^ (3 / 323 : ℝ)) ≤ ρ := by
  have hthr : Work.BoseBoxFock.closeThresholdFS v μ
      = μ * (dil v μ) ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi) := by
    rw [Work.BoseBoxFock.closeThresholdFS, Kl_inv_sq v hμ hav]
  have h2 : |ρ - μ| ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi) := by
    have hc' : |ρ - μ| ≤ Work.BoseBoxFock.closeThresholdFS v μ := hc
    rwa [hthr] at hc'
  have hpos : 0 < ((2 : ℝ) ^ 14 * Real.pi) := mul_pos (by norm_num) Real.pi_pos
  have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ 14 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hdilnn : (0 : ℝ) ≤ dil v μ := by rw [dil]; positivity
  have hxnn : (0 : ℝ) ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) :=
    mul_nonneg hμ.le (Real.rpow_nonneg hdilnn _)
  have hle : μ * (dil v μ) ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi)
      ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) := by
    rw [div_le_iff₀ hpos]
    nlinarith [hxnn, h1le]
  have h4 : -(ρ - μ) ≤ |ρ - μ| := neg_le_abs _
  have h6 : -(ρ - μ) ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) := le_trans (le_trans h4 h2) hle
  linarith [h6]

/-- `CloseCondFS` fails only on `FarCondFS` (the two regions cover `[0,∞)`). -/
lemma farCondFS_of_not_close {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hc : ¬ Work.BoseBoxFock.CloseCondFS v μ ρ) : Work.BoseBoxFock.FarCondFS v μ ρ := by
  rw [Work.BoseBoxFock.CloseCondFS] at hc
  rw [Work.BoseBoxFock.FarCondFS]
  exact le_of_lt (not_le.mp hc)

/-! ## 4. The node -/

/-- **`NodeRestrictedB` from the corrected residuals at the honest model.**  The
`n ≤ 2μℓ³` input of `RB4boxDomAt` comes from `NodeB1B`'s first conjunct
(`eq:apriorinn+`) and the window-factor threshold
(`Work.BoseFixB2.DvApriori.exists_window_factor_le`). -/
theorem nodeRestrictedB_of_residualsFS {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : ScatSol v} {R J' : ℝ} (hav : 0 < a v) (hR : 0 ≤ R) (hJ' : lhyC < J')
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (hB1 : NodeB1B v h J')
    (hdom : RB4boxDomAt v h R J' fc fu HM)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hview : ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε →
      (HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (h5 : RB5FS v h R (HonestBoxFam v h fc fu HM))
    (h67 : RB67FS v h R (HonestBoxFam v h fc fu HM)) :
    ∃ η₀ : ℝ, 1 / 2000 < η₀ ∧ η₀ < 2 / 323 ∧
      ∃ C : ℝ, 0 ≤ C ∧ NodeRestrictedB v h J' η₀ C := by
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
        ≤ (HonestBoxFam v h fc fu HM μ).valFS ρ.1 * normB v μ n Φ := by
    intro ρ
    have hN := normB_nonneg v μ n Φ
    by_cases hc : Work.BoseBoxFock.CloseCondFS v μ ρ.1
    · have hCb : CloseBoundR v R μ C₆ ρ.1 ≤ (HonestBoxFam v h fc fu HM μ).valFS ρ.1 :=
        KzValFS_le_of_bound (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
          (HonestBoxFam v h fc fu HM μ).E (HonestBoxFam v h fc fu HM μ).gHat0 ρ.1 hne
          (fun f hf _ => hclose μ hAdm₆ hv ρ.1 ρ.2 hc f hf)
      have hAbs := AbsorbClose (a := a v) (ℓ := ell v μ) (t := dil v μ) (μ := μ) (R := R)
        (C₄ := Cd) (C₆ := C₆) (K := bigK (a v) R Cd C₆) (η₀ := 1 / 1800) (ρ := ρ.1)
        hav hℓ hμ hR hCd hC₆ (by norm_num) (by norm_num) (by norm_num) hdilpos hdil1 le_rfl ρ.2
        (le_of_eq (by rw [dil])) (closeCondFS_lower hμ hav hc)
      rw [← errKafz_eq_errAbs v hμ hav, ← Lambda_ell3' v,
        ← fsX_sq v hμ hav, ← errExp_eq] at hAbs
      exact mul_le_mul_of_nonneg_right (le_trans hAbs hCb) hN
    · have hfc : Work.BoseBoxFock.FarCondFS v μ ρ.1 := farCondFS_of_not_close hc
      have hFb : FarBound v μ ≤ (HonestBoxFam v h fc fu HM μ).valFS ρ.1 :=
        KzValFS_le_of_bound (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
          (HonestBoxFam v h fc fu HM μ).E (HonestBoxFam v h fc fu HM μ).gHat0 ρ.1 hne
          (fun f hf _ => hfar μ hAdm₅ hv ρ.1 ρ.2 hfc f hf)
      have hAbs := AbsorbFar (a := a v) (ℓ := ell v μ) (t := dil v μ) (μ := μ) (R := R)
        (C₄ := Cd) (C₆ := C₆) (K := bigK (a v) R Cd C₆) (η₀ := 1 / 1800)
        hav hℓ hμ hR hCd hC₆ (by norm_num) (by norm_num) (by norm_num) hdilpos hdil1 le_rfl
      rw [← errKafz_eq_errAbs v hμ hav, ← Lambda_ell3' v, ← FarBound_eq' v μ] at hAbs
      exact mul_le_mul_of_nonneg_right (le_trans hAbs hFb) hN
  have hci : (ell3 v μ * Lambda (a v) (bigK (a v) R Cd C₆) (1 / 1800) μ
        + errKafz v R μ Cd) * normB v μ n Φ
      ≤ ⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}),
          (HonestBoxFam v h fc fu HM μ).valFS ρ.1 * normB v μ n Φ := by
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
              (HonestBoxFam v h fc fu HM μ).valFS ρ.1 * normB v μ n Φ := hci
        _ ≤ wordB v h μ n Φ + errKafz v R μ Cd * normB v μ n Φ := hbridge
    linarith
  rw [BoxBoundB]
  exact hmain

end Work.BoseFixR

import Mathlib
import Submission.Work.OddCurve.Free.Step3Class
import Submission.Work.OddVolterra.Free.lowSlopeCurveAssembly800
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddVolterra.Free.anchorRadialDevBound
import Submission.Work.OddVolterra.Free.glueDataBounds
import Submission.Work.OddVolterra.Free.glueDataSmoothLinear
import Submission.Work.OddVolterra.Free.radialPairPackage
import Submission.Work.OddVolterra.Free.solR_eq_anchor_cap_lt
import Submission.Work.OddVolterra.Free.envProfileFree_hgraph
import Submission.Work.OddVolterra.Free.lowSlopesDatumFree
import Submission.Work.OddVolterra.Free.momentEqs_transfer_free_const
import Submission.Work.OddCurve.Free.lowSlopeCurveAssembly
import Submission.Work.OddCurve.Free.Step3Pieces
import Submission.Work.OddCurve.LowSlope.radial_system_sharp_c2
import Submission.Work.OddCurve.LowSlope.radonPhiRhoNewEq
import Submission.Work.OddCurve.LowSlope.radonPsiRhoNewEq
import Submission.Work.OddCurve.LowSlope.radonInverseRhoNewEq
import Submission.Work.OddCurve.LowSlope.anchorData
import Submission.Work.OddCurve.LowSlope.glue_deviations_eq
import Submission.Work.OddCurve.Free.deltaCapAndSupport
import Submission.Work.OddCurveB.Step3.glue_vanish_near_pi_div_two
import Submission.Work.OddVolterra.Free.radialPiece_deriv_neg_and_shape
import Submission.Work.OddVolterra.Free.strictMonoOn_rhoNew
import Submission.Work.OddVolterra.Free.anchorDatum_eq_ball_of_le_four_fifths
import Submission.Work.OddVolterra.Free.contDiffOn_rhoNew
import Submission.Work.OddVolterra.Free.ballDatum_rhoNew
-- TEMP: import Submission.Work.OddVolterra.Free.lowSlopeCurveAssembly800

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 4000000

noncomputable section

theorem lowSlopeThreeFreeC_internal (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y : ℝ → ℝ,
      Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h → h ≠ 0 →
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      Work.OddCurve.LowSlope.CloseToProfileX X →
      Work.OddCurve.LowSlope.CloseToProfileX Y →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
          Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
      ∃ x y : ℝ → ℝ,
        Work.OddCurve.Free.IsEnvelopeCurveFree h x y ∧
          Work.OddCurve.LowSlope.CloseToProfileX x ∧
          Work.OddCurve.LowSlope.CloseToProfileX y ∧
          (∀ s : ℝ, 0 < s → s ≤ 1 →
            Work.OddCurve.momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) s =
              Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
          (∀ s : ℝ, 0 < s → s ≤ 1 →
            Work.OddCurve.momentB n h x y (Work.OddVolterra.Free.envProfileFree h x y) s = 0) := by
  classical
  -- ## the constants
  obtain ⟨C₁, hC₁pos, hdev⟩ := anchorRadialDevBound n hn
  obtain ⟨Kg, hKgpos, hglue⟩ := glueDataBounds n hn
  obtain ⟨Ks, hKspos, hglueLin⟩ := glueDataSmoothLinear n hn
  obtain ⟨Crp, hCrppos, hrp⟩ := radialPairPackage n hn
  obtain ⟨η₁, hη₁pos, hη₁⟩ := radialPiece_deriv_neg_and_shape
  set G : ℝ := max Kg Ks + 1 with hGdef
  have hGpos : 0 < G := by rw [hGdef]; linarith [le_max_left Kg Ks, hKgpos]
  have hG1 : 1 ≤ G := by rw [hGdef]; linarith [le_max_left Kg Ks, hKgpos]
  have hKgG : Kg ≤ G := by rw [hGdef]; linarith [le_max_left Kg Ks]
  have hKsG : Ks ≤ G := by rw [hGdef]; linarith [le_max_right Kg Ks]
  set K : ℝ := (3 * Crp + 3) * G * (C₁ + 1) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hC₁K : C₁ ≤ K := by
    rw [hKdef]
    have h3 : (1 : ℝ) ≤ 3 * Crp + 3 := by linarith
    have h1 : (1 : ℝ) * 1 ≤ (3 * Crp + 3) * G := mul_le_mul h3 hG1 (by norm_num) (by linarith)
    have h2 : (1 : ℝ) ≤ (3 * Crp + 3) * G := by linarith
    calc C₁ ≤ C₁ + 1 := by linarith
      _ = 1 * (C₁ + 1) := by ring
      _ ≤ ((3 * Crp + 3) * G) * (C₁ + 1) := mul_le_mul_of_nonneg_right h2 (by linarith)
  have hGK : G * (C₁ + 1) ≤ K := by
    rw [hKdef]
    have h3 : (1 : ℝ) ≤ 3 * Crp + 3 := by linarith
    have h4 : (1 : ℝ) * G ≤ (3 * Crp + 3) * G := mul_le_mul_of_nonneg_right h3 hGpos.le
    calc G * (C₁ + 1) = (1 * G) * (C₁ + 1) := by ring
      _ ≤ ((3 * Crp + 3) * G) * (C₁ + 1) := mul_le_mul_of_nonneg_right h4 (by linarith)
      _ = (3 * Crp + 3) * G * (C₁ + 1) := by ring
  -- ## the small number
  set ε : ℝ := min (1 / 800) (min η₁ (1 / 1000) / (K + 1)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (by norm_num) (div_pos (lt_min hη₁pos (by norm_num)) (by linarith))
  have hε800 : ε ≤ 1 / 800 := by rw [hεdef]; exact min_le_left _ _
  have hKε : K * ε ≤ min η₁ (1 / 1000) := by
    have hle : ε ≤ min η₁ (1 / 1000) / (K + 1) := by rw [hεdef]; exact min_le_right _ _
    have hK1 : 0 < K + 1 := by linarith
    have h2 : ε * (K + 1) ≤ min η₁ (1 / 1000) := by
      calc ε * (K + 1) ≤ (min η₁ (1 / 1000) / (K + 1)) * (K + 1) :=
            mul_le_mul_of_nonneg_right hle hK1.le
        _ = min η₁ (1 / 1000) := by field_simp
    nlinarith [h2, hKpos, hεpos]
  have hνε₁ : K * ε ≤ η₁ := le_trans hKε (min_le_left _ _)
  have hνε1000 : K * ε ≤ 1 / 1000 := le_trans hKε (min_le_right _ _)
  have hC₁ε : C₁ * ε ≤ 1 := by nlinarith [hC₁K, hεpos, hνε1000]
  refine ⟨ε, hεpos, ?_⟩
  intro h X Y hb hne H hcX hcY hAeq hBeq
  -- ## the glued data size
  set σ : ℝ := G * (C₁ + 1) * ε with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  have hσK : σ ≤ K * ε := by rw [hσdef]; nlinarith [hGK, hεpos]
  have hσ8 : σ ≤ 1 / 8 := by linarith [hσK, hνε1000]
  have hσ20 : σ ≤ 1 / 20 := by linarith [hσK, hνε1000]
  have h3σ : 3 * σ ≤ K * ε := by nlinarith [hσK, hKpos, hεpos]
  -- ## the anchor's radial function
  obtain ⟨ρa, hρapos, hρa0, hρasm, hρamono, hρagraph, hρain, hρawaist⟩ :=
    Work.OddCurve.LowSlope.exists_radialFunction_anchor (h := h) (X := X) (Y := Y) H
  have hanc : IsAnchorRadial h X Y ρa := ⟨hρapos, hρasm, hρamono, hρagraph, hρa0⟩
  have hρasm1 : ContDiffOn ℝ 1 ρa (Set.Ioo (-1 : ℝ) 1) := hρasm.of_le (by simp)
  have hdevb := hdev hb hne H hcX hcY hAeq hBeq hanc
  -- ## the glued data: value, derivative and smoothness bounds
  have hglueBd := hglue (ε := ε) (C₁ := C₁) (h := h) (X := X) (Y := Y) (ρ := ρa)
    hεpos hC₁ε hb hne H hcX hcY hAeq hBeq hanc hdevb
  obtain ⟨hglueAsm, hglueBsm, hglueLbd⟩ := hglueLin (ε := ε) (C₁ := C₁) (h := h) (X := X)
    (Y := Y) (ρ := ρa) hεpos hC₁ε hb hne H hcX hcY hAeq hBeq hanc hdevb
  -- ## the two-power data, abbreviated
  set gA : ℝ → ℝ := Work.OddCurve.LowSlope.glueA n ρa with hgA
  set gB : ℝ → ℝ := Work.OddCurve.LowSlope.glueB n ρa with hgB
  have hgAsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gA
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hglueAsm
  have hgBsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gB
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hglueBsm
  have hvan : ∀ α ∈ Set.Ioo (Real.pi / 2 - 1 / 4) (Real.pi / 2 + 1 / 4),
      gA α = 0 ∧ gB α = 0 :=
    Work.OddCurveB.Step3.glue_vanish_near_pi_div_two n hn H hanc
  have hKgsin : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |gA α| ≤ σ ∧ |gB α| ≤ σ := by
    intro α hα
    obtain ⟨h1, h2, -, -, -, -⟩ := hglueBd α hα
    have hb1 : Kg * (C₁ + 1) * ε ≤ σ := by rw [hσdef]; nlinarith [hKgG, hεpos, hC₁pos]
    exact ⟨le_trans h1 hb1, le_trans h2 hb1⟩
  have hKgd1 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv gA α| ≤ σ ∧ |deriv gB α| ≤ σ := by
    intro α hα
    obtain ⟨-, -, h1, -, h2, -⟩ := hglueBd α hα
    have hb1 : Kg * (C₁ + 1) * ε ≤ σ := by rw [hσdef]; nlinarith [hKgG, hεpos, hC₁pos]
    exact ⟨le_trans h1 hb1, le_trans h2 hb1⟩
  have hKgd2 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (deriv gA) α| ≤ σ ∧ |deriv (deriv gB) α| ≤ σ := by
    intro α hα
    obtain ⟨-, -, -, h1, -, h2⟩ := hglueBd α hα
    have hb1 : Kg * (C₁ + 1) * ε ≤ σ := by rw [hσdef]; nlinarith [hKgG, hεpos, hC₁pos]
    exact ⟨le_trans h1 hb1, le_trans h2 hb1⟩
  have hKgsin1 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv gA α| ≤ σ * Real.sin α := by
    intro α hα
    obtain ⟨h1, -⟩ := hglueLbd α hα
    have hsin0 : 0 ≤ Real.sin α :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, Real.pi_pos]⟩
    have hb1 : Ks * (C₁ + 1) * ε * Real.sin α ≤ σ * Real.sin α := by
      rw [hσdef]
      have h0 : 0 ≤ (C₁ + 1) * ε * Real.sin α := by positivity
      calc Ks * (C₁ + 1) * ε * Real.sin α = Ks * ((C₁ + 1) * ε * Real.sin α) := by ring
        _ ≤ G * ((C₁ + 1) * ε * Real.sin α) := mul_le_mul_of_nonneg_right hKsG h0
        _ = G * (C₁ + 1) * ε * Real.sin α := by ring
    exact le_trans h1 hb1
  have hKgsin1B : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv gB α| ≤ σ * Real.sin α := by
    intro α hα
    obtain ⟨-, h1⟩ := hglueLbd α hα
    have hsin0 : 0 ≤ Real.sin α :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, Real.pi_pos]⟩
    have hb1 : Ks * (C₁ + 1) * ε * Real.sin α ≤ σ * Real.sin α := by
      rw [hσdef]
      have h0 : 0 ≤ (C₁ + 1) * ε * Real.sin α := by positivity
      calc Ks * (C₁ + 1) * ε * Real.sin α = Ks * ((C₁ + 1) * ε * Real.sin α) := by ring
        _ ≤ G * ((C₁ + 1) * ε * Real.sin α) := mul_le_mul_of_nonneg_right hKsG h0
        _ = G * (C₁ + 1) * ε * Real.sin α := by ring
    exact le_trans h1 hb1
  -- ## the radial pair of the reconstruction
  obtain ⟨R, r, hReq, hreq, hRsm, hrsm, hRsm', hrsm', hRsys0, hRend0, hbnd0, hlog0⟩ :=
    hrp (A := gA) (B := gB) (σ := σ) (δ₁ := σ) (δ₂ := σ)
      hσpos hσ8 hσpos.le hσ20 hσpos.le hgAsm hgBsm hKgsin hKgd1 hKgd2 hKgsin1 hKgsin1B
      (by rw [hgA]; exact Work.OddCurve.LowSlope.glueA_at_pi_div_two hρa0)
      (by rw [hgB]; exact Work.OddCurve.LowSlope.glueB_at_pi_div_two n ρa) hvan
  -- ## the bounds for the pair
  have hupR : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |R α - 1| ≤ K * ε := by
    intro α hα
    rw [hReq]
    have h := (Work.OddCurve.LowSlope.rsc2_bounds_core n hn hσpos hσ8 hσpos.le hσpos.le
      hgAsm hgBsm (fun β hβ => (hKgsin β hβ).1) (fun β hβ => (hKgsin β hβ).2)
      (fun β hβ => (hKgd1 β hβ).1) (fun β hβ => (hKgd1 β hβ).2)
      (fun β hβ => (hKgd2 β hβ).1) (fun β hβ => (hKgd2 β hβ).2) hα).1
    have h2 : 3 * σ / ((n : ℝ) + 1) ≤ 3 * σ := by
      have h0 : (0 : ℝ) ≤ 3 * σ := by linarith [hσpos]
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact div_le_self h0 h1
    linarith [h, h2, h3σ]
  have hupr : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |r α - 1| ≤ K * ε := by
    intro α hα
    rw [hreq]
    have h := (Work.OddCurve.LowSlope.rsc2_bounds_core n hn hσpos hσ8 hσpos.le hσpos.le
      hgAsm hgBsm (fun β hβ => (hKgsin β hβ).1) (fun β hβ => (hKgsin β hβ).2)
      (fun β hβ => (hKgd1 β hβ).1) (fun β hβ => (hKgd1 β hβ).2)
      (fun β hβ => (hKgd2 β hβ).1) (fun β hβ => (hKgd2 β hβ).2) hα).2.1
    have h2 : 3 * σ / ((n : ℝ) + 1) ≤ 3 * σ := by
      have h0 : (0 : ℝ) ≤ 3 * σ := by linarith [hσpos]
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact div_le_self h0 h1
    linarith [h, h2, h3σ]
  have hpg : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv R α| ≤ K * ε ∧ |deriv r α| ≤ K * ε := by
    intro α hα
    obtain ⟨-, -, h3, h4, -, -⟩ :=
      Work.OddCurve.LowSlope.rsc2_bounds_core n hn hσpos hσ8 hσpos.le hσpos.le
        hgAsm hgBsm (fun β hβ => (hKgsin β hβ).1) (fun β hβ => (hKgsin β hβ).2)
        (fun β hβ => (hKgd1 β hβ).1) (fun β hβ => (hKgd1 β hβ).2)
        (fun β hβ => (hKgd2 β hβ).1) (fun β hβ => (hKgd2 β hβ).2) hα
    have h2 : 3 * σ / ((n : ℝ) + 1) ≤ 3 * σ := by
      have h0 : (0 : ℝ) ≤ 3 * σ := by linarith [hσpos]
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact div_le_self h0 h1
    constructor
    · rw [hReq]; linarith [h3, h2, h3σ]
    · rw [hreq]; linarith [h4, h2, h3σ]
  have hbnd : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |R α - 1| ≤ K * ε ∧ |deriv R α| ≤ K * ε * α ∧ |deriv (deriv R) α| ≤ K * ε ∧
      |r α - 1| ≤ K * ε ∧ |deriv r α| ≤ K * ε * α ∧ |deriv (deriv r) α| ≤ K * ε := by
    intro α hα
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbnd0 α hα
    have h7 : Crp * (σ + σ + σ) ≤ K * ε := by
      have h8 : Crp * (σ + σ + σ) ≤ 3 * Crp * σ := by nlinarith [hσpos, hCrppos]
      have h9 : 3 * Crp * σ ≤ K * ε := by
        have h0 : 3 * Crp * σ ≤ (3 * Crp + 3) * σ := by nlinarith [hσpos.le, hCrppos]
        have h1 : (3 * Crp + 3) * σ = K * ε := by rw [hσdef, hKdef]; ring
        linarith [h0, h1]
      linarith [h8, h9]
    have h7' : Crp * (σ + σ + σ) * α ≤ K * ε * α := mul_le_mul_of_nonneg_right h7 hα.1
    exact ⟨hupR α hα, by linarith [h2, h7'], by linarith [h3, h7],
      hupr α hα, by linarith [h5, h7'], by linarith [h6, h7]⟩
  have hRpos : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 < R α := by
    intro α hα
    have h := neg_le_of_abs_le (hupR α hα)
    linarith [h, hνε1000]
  have hrpos : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 < r α := by
    intro α hα
    have h := neg_le_of_abs_le (hupr α hα)
    linarith [h, hνε1000]
  -- ## the monotonicity and shape conditions for the radial pieces
  have hmonoR : ∀ τ : ℝ, 0 < τ → τ < 3 / 4 →
      deriv (fun t : ℝ => R (Real.arctan t) * Real.cos (Real.arctan t)) τ < 0 :=
    (hη₁ R hRsm (fun α hα => ⟨le_trans (hbnd α hα).1 hνε₁,
      le_trans (hbnd α hα).2.1 (mul_le_mul_of_nonneg_right hνε₁ hα.1), le_trans (hbnd α hα).2.2.1 hνε₁⟩)).1
  have hmonor : ∀ τ : ℝ, 0 < τ → τ < 3 / 4 →
      deriv (fun t : ℝ => r (Real.arctan t) * Real.cos (Real.arctan t)) τ < 0 :=
    (hη₁ r hrsm (fun α hα => ⟨le_trans (hbnd α hα).2.2.2.1 hνε₁,
      le_trans (hbnd α hα).2.2.2.2.1 (mul_le_mul_of_nonneg_right hνε₁ hα.1), le_trans (hbnd α hα).2.2.2.2.2 hνε₁⟩)).1
  have hshapeR : ∀ τ : ℝ, 0 < τ → τ < 3 / 4 →
      0 < 2 * (deriv (fun t : ℝ => R (Real.arctan t) * Real.cos (Real.arctan t)) τ) ^ 2 -
        (R (Real.arctan τ) * Real.cos (Real.arctan τ)) *
          deriv (deriv (fun t : ℝ => R (Real.arctan t) * Real.cos (Real.arctan t))) τ :=
    (hη₁ R hRsm (fun α hα => ⟨le_trans (hbnd α hα).1 hνε₁,
      le_trans (hbnd α hα).2.1 (mul_le_mul_of_nonneg_right hνε₁ hα.1), le_trans (hbnd α hα).2.2.1 hνε₁⟩)).2
  have hshaper : ∀ τ : ℝ, 0 < τ → τ < 3 / 4 →
      0 < 2 * (deriv (fun t : ℝ => r (Real.arctan t) * Real.cos (Real.arctan t)) τ) ^ 2 -
        (r (Real.arctan τ) * Real.cos (Real.arctan τ)) *
          deriv (deriv (fun t : ℝ => r (Real.arctan t) * Real.cos (Real.arctan t))) τ :=
    (hη₁ r hrsm (fun α hα => ⟨le_trans (hbnd α hα).2.2.2.1 hνε₁,
      le_trans (hbnd α hα).2.2.2.2.1 (mul_le_mul_of_nonneg_right hνε₁ hα.1), le_trans (hbnd α hα).2.2.2.2.2 hνε₁⟩)).2
  -- ## the cap identities for the two-power data
  have hjunCap : ∀ c ∈ Set.Ioo ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹)
        ((Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹),
      Work.OddCurve.LowSlope.radonPhi n ρa c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρa c = 0 :=
    fun c hc => Work.OddCurve.LowSlope.anchorData_junction_cap n hn H hρapos hρasm1 hρamono
      hρagraph hAeq hBeq hc
  have hcapHi : (4 : ℝ) / 5 < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ := by
    have hpos : 0 < Real.sqrt (1 + (7 / 10 : ℝ) ^ 2) := Real.sqrt_pos.mpr (by norm_num)
    rw [show (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ = 1 / Real.sqrt (1 + (7 / 10 : ℝ) ^ 2)
      by ring, lt_div_iff₀ hpos]
    have hsq : Real.sqrt (1 + (7 / 10 : ℝ) ^ 2) ^ 2 = 1 + (7 / 10 : ℝ) ^ 2 :=
      Real.sq_sqrt (by norm_num)
    nlinarith [hsq]
  have hAcap : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), Real.cos α ≤ 4 / 5 →
      gA α = ρa (Real.cos α) ^ (2 * n + 2) + ρa (-(Real.cos α)) ^ (2 * n + 2) - 2 := by
    intro α _ hc
    rcases lt_or_eq_of_le hc with hlt | heq
    · rw [hgA]; exact Work.OddCurve.LowSlope.glueA_of_lt hlt
    · have hge : (4 : ℝ) / 5 ≤ Real.cos α := heq.ge
      rw [hgA, Work.OddCurve.LowSlope.glueA_of_ge hge]
      exact Work.OddCurve.LowSlope.GlueA_eq_cap n hn hρasm (fun c hc' => hjunCap c hc')
        (by rw [heq]; norm_num) (by rw [heq]; exact hcapHi)
  have hBcap : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), Real.cos α ≤ 4 / 5 →
      gB α = ρa (Real.cos α) ^ (2 * n + 1) - ρa (-(Real.cos α)) ^ (2 * n + 1) := by
    intro α _ hc
    rcases lt_or_eq_of_le hc with hlt | heq
    · rw [hgB]; exact Work.OddCurve.LowSlope.glueB_of_lt hlt
    · have hge : (4 : ℝ) / 5 ≤ Real.cos α := heq.ge
      rw [hgB, Work.OddCurve.LowSlope.glueB_of_ge hge]
      exact Work.OddCurve.LowSlope.GlueB_eq_cap n hn hρasm (fun c hc' => hjunCap c hc')
        (by rw [heq]; norm_num) (by rw [heq]; exact hcapHi)
  have hsols : ∀ α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos α ≤ 4 / 5 →
      Work.OddCurve.LowSlope.solR n gA gB α = ρa (Real.cos α) ∧
      Work.OddCurve.LowSlope.solr n gA gB α = ρa (-(Real.cos α)) :=
    Work.OddVolterra.Free.solR_eq_anchor_cap_lt n hn hAcap hBcap hρapos
  have hRend : R (Real.pi / 2) = 1 := by
    rw [hReq]
    exact Work.OddCurve.LowSlope.solR_end n
      (by rw [hgA]; exact Work.OddCurve.LowSlope.glueA_at_pi_div_two hρa0)
      (by rw [hgB]; exact Work.OddCurve.LowSlope.glueB_at_pi_div_two n ρa)
  have hrend : r (Real.pi / 2) = 1 := by
    rw [hreq]
    exact Work.OddCurve.LowSlope.solr_end n
      (by rw [hgA]; exact Work.OddCurve.LowSlope.glueA_at_pi_div_two hρa0)
      (by rw [hgB]; exact Work.OddCurve.LowSlope.glueB_at_pi_div_two n ρa)
  -- ## the cap identity for the reconstructed profile
  have hcap : ∀ u : ℝ, |u| ≤ 4 / 5 →
      Work.OddCurve.LowSlope.rhoNew R r u = ρa u := by
    intro u hu
    have huI : -(4 / 5 : ℝ) ≤ u ∧ u ≤ 4 / 5 := abs_le.mp hu
    rcases lt_trichotomy u 0 with hu0 | hu0 | hu0
    · rw [Work.OddCurve.LowSlope.rhoNew_of_neg hu0]
      have hα : Real.arccos (-u) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨Real.arccos_pos.mpr (by linarith [huI.1]),
          Real.arccos_lt_pi_div_two.mpr (by linarith [huI.1])⟩
      have hcos : Real.cos (Real.arccos (-u)) = -u :=
        Real.cos_arccos (by linarith [huI.2]) (by linarith [hu0])
      have h1 := (hsols _ hα (by rw [hcos]; linarith [huI.1])).2
      rw [← hreq] at h1
      rw [h1, hcos, neg_neg]
    · subst hu0
      rw [Work.OddCurve.LowSlope.rhoNew_of_nonneg le_rfl, Real.arccos_zero, hRend, hρa0]
    · rw [Work.OddCurve.LowSlope.rhoNew_of_nonneg hu0.le]
      have hα : Real.arccos u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨Real.arccos_pos.mpr (by linarith [huI.2]),
          Real.arccos_lt_pi_div_two.mpr hu0⟩
      have hcos : Real.cos (Real.arccos u) = u :=
        Real.cos_arccos (by linarith [huI.1]) (by linarith [huI.2])
      have h1 := (hsols _ hα (by rw [hcos]; linarith [huI.2])).1
      rw [← hReq] at h1
      rw [h1, hcos]
  -- ## strict monotonicity and smoothness of the reconstructed radial function
  have hρmonoNew : StrictMonoOn (fun u : ℝ =>
      Work.OddCurve.LowSlope.rhoNew R r u * u) (Set.Ioo (-1 : ℝ) 1) :=
    strictMonoOn_rhoNew hRsm hrsm hRpos hrpos hmonoR hmonor hρapos hρamono hcap
  have hwin : ∀ α ∈ Set.Ioo (Real.pi / 2 - 1 / 4) (Real.pi / 2 + 1 / 4), R α = 1 ∧ r α = 1 := by
    intro α hα
    constructor
    · rw [hReq]
      exact Work.OddVolterra.Free.solR_eq_one_of_data_eq_zero n (hvan α hα).1 (hvan α hα).2
    · rw [hreq]
      exact Work.OddVolterra.Free.solr_eq_one_of_data_eq_zero n (hvan α hα).1 (hvan α hα).2
  have hsin_quarter : Real.sin (1 / 4) = Real.cos (Real.pi / 2 - 1 / 4) :=
    (Real.cos_pi_div_two_sub (1 / 4)).symm
  have hsmNew : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.rhoNew R r) (Set.Ioo (-1 : ℝ) 1) := by
    refine contDiffOn_rhoNew hRsm hrsm ⟨Real.sin (1 / 4),
      Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three]), fun u hu => ?_⟩
    have huI := abs_lt.mp hu
    have harc : Real.arccos (Real.sin (1 / 4)) = Real.pi / 2 - 1 / 4 := by
      rw [hsin_quarter, Real.arccos_cos (by linarith [Real.pi_gt_three])
        (by linarith [Real.pi_gt_three])]
    have harg : ∀ v : ℝ, 0 < v → v < Real.sin (1 / 4) →
        Real.pi / 2 - 1 / 4 < Real.arccos v := by
      intro v hv0 hv
      have hkey := Real.arccos_lt_arccos (x := v) (y := Real.sin (1 / 4))
        (by linarith [hv0]) hv (Real.sin_le_one (1 / 4))
      rwa [harc] at hkey
    rcases lt_or_ge 0 u with hu0 | hu0
    · rw [Work.OddCurve.LowSlope.rhoNew_of_nonneg hu0.le]
      have hlt : Real.arccos u < Real.pi / 2 + 1 / 4 := by
        have h := Real.arccos_lt_pi_div_two.mpr hu0
        linarith
      exact (hwin _ ⟨harg u hu0 huI.2, hlt⟩).1
    · rcases lt_or_eq_of_le hu0 with hu0' | rfl
      · rw [Work.OddCurve.LowSlope.rhoNew_of_neg hu0']
        have hnu : -u < Real.sin (1 / 4) := by linarith [huI.1, hu0']
        have hpos : 0 < -u := neg_pos.mpr hu0'
        have hlt : Real.arccos (-u) < Real.pi / 2 + 1 / 4 := by
          have h := Real.arccos_lt_pi_div_two.mpr hpos
          linarith
        exact (hwin _ ⟨harg (-u) hpos hnu, hlt⟩).2
      · rw [Work.OddCurve.LowSlope.rhoNew_of_nonneg le_rfl, Real.arccos_zero, hRend]
  -- ## the glued RadialSystem
  have hRsysG : Work.OddRadon.RadialSystem n (Work.OddCurve.LowSlope.GluePhi n ρa)
      (Work.OddCurve.LowSlope.GluePsi n ρa) R r := by
    intro α hα
    obtain ⟨h1, h2⟩ := Work.OddCurve.LowSlope.glue_deviations_eq n hn hρasm α hα
    refine ⟨?_, ?_⟩
    · rw [h1, ← hgA]; exact (hRsys0 α hα).1
    · rw [h2, ← hgB]; exact (hRsys0 α hα).2
  -- ## the ball's datum for the reconstruction
  have hball : ∀ c : ℝ, (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹ ≤ c → c < 1 →
      Work.OddCurve.LowSlope.radonPhi n (Work.OddCurve.LowSlope.rhoNew R r) c =
        Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n (Work.OddCurve.LowSlope.rhoNew R r) c = 0 := by
    have hthr : (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹
        = (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ := by norm_num [Work.OddEnvelope.tau]
    rw [hthr]
    exact ballDatum_rhoNew n hn hρasm
      (Work.OddVolterra.Free.junctionWindow n hn H hAeq hBeq hanc)
      (anchorDatum_eq_ball_of_le_four_fifths n hn hb hne H hAeq hBeq hanc) hsmNew hRsysG
  -- ## the two-piece curve
  have hb3 : Work.OddVolterra.Existence.IsSmallFlatBumpThree n (1 / 800) h :=
    ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k (by omega) s) hε800, hb.2.2.2⟩
  have hcurve_bnd : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |R α - 1| ≤ 1 / 800 ∧ |deriv R α| ≤ 1 / 800 ∧ |deriv (deriv R) α| ≤ 1 / 800 ∧
      |r α - 1| ≤ 1 / 800 ∧ |deriv r α| ≤ 1 / 800 ∧ |deriv (deriv r) α| ≤ 1 / 800 := by
    intro α hα
    obtain ⟨h1, -, h3, h4, -, h6⟩ := hbnd α hα
    obtain ⟨h7, h8⟩ := hpg α hα
    exact ⟨by linarith [h1, hνε1000], by linarith [h7, hνε1000], by linarith [h3, hνε1000],
      by linarith [h4, hνε1000], by linarith [h8, hνε1000], by linarith [h6, hνε1000]⟩
  have hjunc : ∀ τ : ℝ, 3 / 4 ≤ τ → τ ≤ 4 / 5 →
      Y τ = R (Real.arctan τ) * Real.cos (Real.arctan τ) ∧
      X τ = r (Real.arctan τ) * Real.cos (Real.arctan τ) := by
    intro τ h1 h2
    have hτpos : 0 < τ := by norm_num at h1 ⊢; linarith
    have hz : h τ = 0 := by
      rcases lt_or_eq_of_le h2 with hlt | heq
      · by_contra hne'
        have hmem := hb.2.1 (Function.mem_support.mpr hne')
        have hτ4 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
          norm_num [Work.OddVolterra.tau]
        rw [hτ4] at hmem
        linarith [hmem.1, hlt]
      · subst heq
        obtain ⟨η, hηpos, hflat⟩ := hb.2.2.2
        have hτ4 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
          norm_num [Work.OddVolterra.tau]
        exact hflat (4 / 5) (by rw [hτ4]) (by rw [hτ4]; linarith)
    obtain ⟨hY, hX⟩ := Work.OddCurve.LowSlope.envelope_chord_eq_radial H hτpos hz hρapos hρagraph
    have hα : Real.arctan τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨Real.arctan_pos.mpr hτpos, Real.arctan_lt_pi_div_two τ⟩
    have hcc : Real.cos (Real.arctan τ) ≤ 4 / 5 := by
      rw [Real.cos_arctan, div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
      have hsq : (3 / 4 : ℝ) ^ 2 ≤ τ ^ 2 := by nlinarith [h1]
      have h2 : (5 / 4 : ℝ) ≤ Real.sqrt (1 + τ ^ 2) := by
        have h5 : (5 / 4 : ℝ) = Real.sqrt ((5 / 4) ^ 2) := by
          rw [Real.sqrt_sq (by norm_num)]
        rw [h5]
        exact Real.sqrt_le_sqrt (by nlinarith [hsq])
      nlinarith [h2]
    obtain ⟨h1', h2'⟩ := hsols _ hα hcc
    have hcos : Real.cos (Real.arctan τ) = (Real.sqrt (1 + τ ^ 2))⁻¹ := by
      rw [Real.cos_arctan, one_div]
    constructor
    · rw [hY, ← hcos, ← h1', hReq]
    · rw [hX, ← hcos, ← h2', hreq]
  -- ## the curve assembly
  obtain ⟨hfr, hcX', hcY'⟩ := lowSlopeCurveAssembly800 n hn
    hb3 H hcX hcY hRsm hrsm hRend hrend hcurve_bnd hjunc hmonoR hmonor hshapeR hshaper
  -- ## the graph identity
  have hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      Work.OddCurve.LowSlope.rhoNew R r u * Real.sqrt (1 - u ^ 2) =
        Work.OddVolterra.Free.envProfileFree h (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
          (Work.OddCurve.LowSlope.lowSlopeCurveY R Y)
          (Work.OddCurve.LowSlope.rhoNew R r u * u) :=
    envProfileFree_hgraph n hn hεpos (mul_pos hKpos hεpos) hνε1000 hb hne H hcX hcY hanc hfr
      (fun α hα => ⟨by have h := neg_le_of_abs_le (hbnd α hα).1; linarith [h, hνε1000],
        by have h := neg_le_of_abs_le (hbnd α hα).2.2.2.1; linarith [h, hνε1000],
        (hbnd α hα).2.1, (hbnd α hα).2.2.2.2.1, (hbnd α hα).2.2.1, (hbnd α hα).2.2.2.2.2⟩)
      hcap
  -- ## the three remaining inputs of the low-slope lemma
  have hzero : ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau → h s = 0 := by
    intro s _ hsle
    by_contra hne'
    have hmem := hb.2.1 (Function.mem_support.mpr hne')
    have hτ : (1 : ℝ) - 2 * Work.OddVolterra.tau = 1 - 2 * Work.OddEnvelope.tau := by
      norm_num [Work.OddVolterra.tau, Work.OddEnvelope.tau]
    have hlt : (1 : ℝ) - 2 * Work.OddEnvelope.tau < s := by rw [← hτ]; exact hmem.1
    linarith [hlt, hsle]
  have hval : Work.OddCurve.momentA n h (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
      (Work.OddCurve.LowSlope.lowSlopeCurveY R Y)
      (Work.OddVolterra.Free.envProfileFree h (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
        (Work.OddCurve.LowSlope.lowSlopeCurveY R Y)) (3 / 4)
      = Work.OddCurve.refConst n / Real.sqrt (1 + (3 / 4) ^ 2) := by
    rw [Work.OddVolterra.Free.momentA_eq_of_agree_free
      (Work.OddCurve.Free.isEnvelopeCurveFree_of_isEnvelopeCurve H) hfr
      (a := 3 / 4) (fun τ hτ => Work.OddCurve.LowSlope.lowSlopeCurve_agree τ hτ) le_rfl
      (by norm_num)]
    rw [Work.OddVolterra.Free.momentA_anchor_eq_free n H (by norm_num : (0 : ℝ) < 3 / 4)]
    exact hAeq (3 / 4) (by norm_num [Work.OddVolterra.tau]) (by norm_num)
  obtain ⟨hlowA, hlowB⟩ := lowSlopesDatumFree n hn (h := h)
    (x := Work.OddCurve.LowSlope.lowSlopeCurveX r X)
    (y := Work.OddCurve.LowSlope.lowSlopeCurveY R Y) (ρ := Work.OddCurve.LowSlope.rhoNew R r)
    (b := 3 / 4) hfr (by norm_num) (by norm_num [Work.OddEnvelope.tau]) hzero
    (fun u hu => by
      rcases le_or_gt 0 u with hu0 | hu0
      · rw [Work.OddCurve.LowSlope.rhoNew_of_nonneg hu0]
        exact hRpos _ ⟨Real.arccos_nonneg u, Real.arccos_le_pi_div_two.mpr (by linarith [hu.1])⟩
      · rw [Work.OddCurve.LowSlope.rhoNew_of_neg hu0]
        exact hrpos _ ⟨Real.arccos_nonneg (-u), Real.arccos_le_pi_div_two.mpr (by linarith [hu.2])⟩)
    (hsmNew.of_le (by norm_num)) hρmonoNew hgraph hball hval
  -- ## the transfer to the transition window
  obtain ⟨hAfree, hBfree⟩ := anchorMomentEqs_free n H hAeq hBeq
  obtain ⟨htrA, htrB⟩ := momentEqs_transfer_free_const n hn
    (Work.OddCurve.Free.isEnvelopeCurveFree_of_isEnvelopeCurve H) hfr
    (by norm_num [Work.OddVolterra.tau])
    (fun τ hτ => Work.OddCurve.LowSlope.lowSlopeCurve_agree τ hτ) hAfree hBfree
  refine ⟨Work.OddCurve.LowSlope.lowSlopeCurveX r X,
    Work.OddCurve.LowSlope.lowSlopeCurveY R Y, hfr, hcX', hcY', ?_, ?_⟩
  · intro s hs hs1
    rcases le_or_gt s (3 / 4) with hle | hgt
    · exact hlowA s hs hle
    · exact htrA s hgt.le hs1
  · intro s hs hs1
    rcases le_or_gt s (3 / 4) with hle | hgt
    · exact hlowB s hs hle
    · exact htrB s hgt.le hs1

end

end Work.OddVolterra.Free

namespace Work.OddCurve.Free

theorem lowSlopeThreeFreeC (n : ℕ) (hn : 1 ≤ n) :
    Work.OddCurve.Free.LowSlopeThreeFreeC n :=
  Work.OddVolterra.Free.lowSlopeThreeFreeC_internal n hn

end Work.OddCurve.Free

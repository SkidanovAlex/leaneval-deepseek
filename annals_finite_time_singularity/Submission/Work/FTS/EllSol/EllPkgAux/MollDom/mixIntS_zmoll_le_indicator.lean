import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllSol.EllPkgAux.wExpCmp
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTDefs
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zMixedDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixed_conv
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchur_pth_window_unif
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.window_E_le_F

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter
open scoped Real Topology

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## The kernel bound and the weight comparison on the logarithmic window -/

/-- The derivative kernel `sKerd δ = (sKer δ)'` is supported in `|·| ≤ δ` and bounded there:
there is a single constant `N > 0` with `|sKerd δ u| ≤ N · 1_{|u| ≤ δ}` for every `u`. -/
theorem sKerd_indicator (δ : ℝ) (hδ : 0 < δ) : ∃ N : ℝ, 0 < N ∧ ∀ u : ℝ,
    |Work.FTS.EllSol.EllPkgAux.sKerd δ u|
      ≤ N * (if |u| ≤ δ then (1 : ℝ) else 0) := by
  obtain ⟨M, hM0, hM⟩ := sKerd_bdd' hδ
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun u => ?_⟩
  by_cases h : |u| ≤ δ
  · rw [if_pos h, mul_one]
    exact le_trans (hM u) (le_max_left _ _)
  · have hzero : Work.FTS.EllSol.EllPkgAux.sKerd δ u = 0 :=
      Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hδ (lt_of_not_ge h)
    rw [if_neg h, mul_zero, hzero, abs_zero]

/-- The weight `w (e^s)² = (1+e^s)^4 e^{-3s}` compared at the two ends of the logarithmic
window `|log z - t| ≤ δ ≤ 1/2`: `w z ² ≤ 10 · w (e^t)²`. -/
theorem w_window_cmp {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) {z t : ℝ} (hz : 0 < z)
    (ht : |Real.log z - t| ≤ δ) :
    (Work.Spaces.w z) ^ 2 ≤ 10 * (Work.Spaces.w (Real.exp t)) ^ 2 := by
  have hlog : Real.exp (Real.log z) = z := Real.exp_log hz
  have h1 : |Real.log z - t| ≤ 1 / 2 := le_trans ht (le_trans hδ1 (by norm_num))
  have h2 := Work.FTS.EllSol.EllPkgAux.wExpCmp (Real.log z) t h1
  rw [hlog] at h2
  have hEt : Real.exp t ≤ 2 * z := by
    have hle : t - Real.log z ≤ 1 / 2 := by
      have h := (abs_le.mp h1).1
      linarith
    have hexp1 : Real.exp (t - Real.log z) ≤ 2 := by
      refine le_trans (Real.exp_le_exp.mpr hle) ?_
      have hsq : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
        rw [sq, ← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2), hsq, Real.exp_one_lt_d9]
    calc Real.exp t = Real.exp (Real.log z + (t - Real.log z)) := by ring_nf
      _ = z * Real.exp (t - Real.log z) := by rw [Real.exp_add, hlog]
      _ ≤ z * 2 := by nlinarith [hexp1, hz.le]
      _ = 2 * z := by ring
  have h3 : (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * ((Work.Spaces.w (Real.exp t)) ^ 2 * (2 * z)) := by
    nlinarith [h2, hEt, hz, sq_nonneg (Work.Spaces.w (Real.exp t))]
  have h4 : (Work.Spaces.w z) ^ 2 * z ≤ (10 * (Work.Spaces.w (Real.exp t)) ^ 2) * z := by
    calc (Work.Spaces.w z) ^ 2 * z ≤ 5 * ((Work.Spaces.w (Real.exp t)) ^ 2 * (2 * z)) := h3
      _ = (10 * (Work.Spaces.w (Real.exp t)) ^ 2) * z := by ring
  exact (mul_le_mul_iff_of_pos_right hz).mp h4

/-! ## Dropping the angular weight `σ_η ≥ 1` -/

/-- `σ_η = sin(2θ)^{-η} ≥ 1` on the open angular interval. -/
private theorem one_le_thEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ σθ θ := by
  rw [Work.FTS.EllipticEst.thEta]
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta)) hsin
    (Real.sin_le_one (2 * θ)) (by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- `σ_η = sin(2θ)^{-η} ≥ 1` almost everywhere on `Iθ = [0, π/2]`. -/
private theorem ae_one_le_thEta :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Iθ), 1 ≤ σθ s := by
  have hEq : MeasureTheory.volume.restrict Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hEq]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => one_le_thEta_Ioo hθ)

/-- Dropping the angular weight `σ_η ≥ 1` costs nothing: for a nonnegative `f` whose
`σ_η`-weighted version is integrable on `Iθ`, `∫_{Iθ} f ≤ ∫_{Iθ} f σ_η`. -/
private theorem integral_le_integral_mul_thEta {f : ℝ → ℝ} (hf : ∀ s : ℝ, 0 ≤ f s)
    (hint : MeasureTheory.Integrable (fun s : ℝ => f s * σθ s)
      (MeasureTheory.volume.restrict Iθ)) :
    (∫ s in Iθ, f s) ≤ ∫ s in Iθ, f s * σθ s := by
  have h := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Iθ)
    (f := fun s : ℝ => f s) (g := fun s : ℝ => f s * σθ s)
    (Filter.Eventually.of_forall hf) hint ?_
  · exact h
  · filter_upwards [ae_one_le_thEta] with s hs
    exact le_mul_of_one_le_right (hf s) hs

/-! ## The main estimate -/

theorem mixIntS_zmoll_le_indicator (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
      Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
        ≤ C * ∫ t : ℝ,
            (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) := by
  have hP0 : Work.FTS.EllSol.EllPkgAux.Params δ ε := hP
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP0
  obtain ⟨KJc, hKJc0, hKJc⟩ := Work.FTS.EllSol.EllPkgAux.kernelJensen
  obtain ⟨C1, hC10, hC1⟩ := zSchur_pth_window_unif G hT hF δ hδ0 hδ1
  obtain ⟨C2, hC20, hC2⟩ := window_E_le_F G hT hF δ hδ0
  refine ⟨KJc * C1 * C2 * 10, by positivity, fun z hz => ?_⟩
  set A : ℝ → ℝ := fun s => zSchur δ (fun w => Work.Spaces.pth G w s) z with hAdef
  have hintA : MeasureTheory.IntegrableOn (fun s : ℝ => (A s) ^ 2 * σθ s) Iθ := by
    rw [hAdef]
    exact (hC1 z hz).1
  have hKJ := hKJc A hintA ε hε0 hε1
  have hid := zmoll_mixed_conv G hT hF δ ε hP z hz
  -- Step 1: insert the convolution identity and apply the angular Jensen/Schur estimate
  have heq : (∫ θ in Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ) ^ 2
          * σθ θ)
      = (∫ θ in Iθ, σθ θ
          * (∫ s in Iθ,
              (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)
                + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * A s) ^ 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    simp only [hAdef]
    rw [hid θ hθ]
    simp only [Work.FTS.EllSol.EllPkgAux.KJ]
    ring
  have h1 : (∫ θ in Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ) ^ 2
          * σθ θ)
      ≤ KJc * (∫ s in Iθ, (A s) ^ 2 * σθ s) := by
    rw [heq]
    exact hKJ
  -- Step 2: the logarithmic-Schur window bound for the angular derivative
  have h2 : (∫ s in Iθ, (A s) ^ 2 * σθ s)
      ≤ C1 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
          (∫ s in Iθ, σθ s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0)) := by
    have h := (hC1 z hz).2
    refine le_of_eq_of_le ?_ h
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    simp only [hAdef]
    ring
  -- Step 3: the weighted Poincaré estimate on the logarithmic window
  have h3 : (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
        (∫ s in Iθ, σθ s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0))
      ≤ C2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
        (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)) :=
    (hC2 z hz).2
  -- Step 4: the radial weight comparison on the window
  have hAngint : ∀ t : ℝ, MeasureTheory.Integrable
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s)
      (MeasureTheory.volume.restrict Iθ) := by
    intro t
    have h0 := hT.2.2.2.2.2.2.2.1 (Real.exp t) (Real.exp_pos t)
    have hwne : (Work.Spaces.w (Real.exp t)) ^ 2 ≠ 0 := by
      have h1 : 0 < Work.Spaces.w (Real.exp t) := by rw [Work.Spaces.w]; positivity
      positivity
    refine (h0.const_mul (((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹)).congr
      (Filter.Eventually.of_forall (fun s => ?_))
    calc ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹
          * ((Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2
              * (Work.Spaces.w (Real.exp t)) ^ 2 * σθ s)
        = ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹ * (Work.Spaces.w (Real.exp t)) ^ 2
            * ((Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s) := by ring
      _ = (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s := by
            rw [inv_mul_cancel₀ hwne, one_mul]
  have hmain : ∀ t : ℝ, (Work.Spaces.w z) ^ 2 * (if |Real.log z - t| ≤ δ then
        (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)
      ≤ 10 * (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) := by
    intro t
    by_cases ht : |Real.log z - t| ≤ δ
    · rw [if_pos ht, if_pos ht]
      have hAB := integral_le_integral_mul_thEta (f := fun s : ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2)
        (fun s => sq_nonneg _) (hAngint t)
      have hBnn : 0 ≤ ∫ s in Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun s hs => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs))
      have hwcmp := w_window_cmp hδ0 hδ1 hz ht
      have hTdef : Work.EllipticEst.Core.ttIntS G (Real.exp t)
          = (Work.Spaces.w (Real.exp t)) ^ 2 * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s) := rfl
      rw [hTdef]
      calc (Work.Spaces.w z) ^ 2 * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s) :=
            mul_le_mul_of_nonneg_left hAB (sq_nonneg _)
        _ ≤ (10 * (Work.Spaces.w (Real.exp t)) ^ 2) * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s) :=
            mul_le_mul_of_nonneg_right hwcmp hBnn
        _ = 10 * ((Work.Spaces.w (Real.exp t)) ^ 2 * (∫ s in Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 * σθ s)) := by ring
    · rw [if_neg ht, if_neg ht]
      simp
  have h4 : (Work.Spaces.w z) ^ 2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
        (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0))
      ≤ 10 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
          Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0)) := by
    have hIntT : MeasureTheory.Integrable (fun t : ℝ => 10 * (if |Real.log z - t| ≤ δ then
        Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0)) MeasureTheory.volume :=
      ((window_ttIntS_integrable G hT hF δ z hδ0 hz).1).const_mul 10
    have hleft_nn : 0 ≤ᵐ[MeasureTheory.volume] (fun t : ℝ => (Work.Spaces.w z) ^ 2 *
        (if |Real.log z - t| ≤ δ then
          (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)) := by
      filter_upwards with t
      by_cases ht : |Real.log z - t| ≤ δ
      · rw [if_pos ht]
        exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun s _ => sq_nonneg _))
      · rw [if_neg ht]
        simp
    have hmono := MeasureTheory.integral_mono_of_nonneg hleft_nn hIntT
      (Filter.Eventually.of_forall hmain)
    calc (Work.Spaces.w z) ^ 2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0))
        = ∫ t : ℝ, (Work.Spaces.w z) ^ 2 * (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ∫ t : ℝ, 10 * (if |Real.log z - t| ≤ δ then
            Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) := hmono
      _ = 10 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0)) := by
          rw [MeasureTheory.integral_const_mul]
  calc Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ) ^ 2
            * σθ θ) := rfl
    _ ≤ (Work.Spaces.w z) ^ 2 * (KJc * (∫ s in Iθ, (A s) ^ 2 * σθ s)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = KJc * ((Work.Spaces.w z) ^ 2 * (∫ s in Iθ, (A s) ^ 2 * σθ s)) := by ring
    _ ≤ KJc * ((Work.Spaces.w z) ^ 2 * (C1 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, σθ s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hKJc0.le
        exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = KJc * C1 * ((Work.Spaces.w z) ^ 2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, σθ s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0))) := by ring
    _ ≤ KJc * C1 * ((Work.Spaces.w z) ^ 2 * (C2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = KJc * C1 * C2 * ((Work.Spaces.w z) ^ 2 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Iθ, (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0))) := by ring
    _ ≤ KJc * C1 * C2 * (10 * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact h4
    _ = (KJc * C1 * C2 * 10) * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0)) := by ring

end Work.FTS.EllSol.EllPkgAux.MollDom

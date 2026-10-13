import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchurWindowDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.window_ttIntS_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Two elementary facts about the logarithmic window -/

/-- The logarithmic window `{|log z - t| ≤ δ}` is the compact interval
`[log z - δ, log z + δ]`. -/
theorem win_window_eq_Icc {δ z : ℝ} :
    {t : ℝ | |Real.log z - t| ≤ δ} = Set.Icc (Real.log z - δ) (Real.log z + δ) := by
  ext t
  rw [Set.mem_ofPred_eq, abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- The logarithmic window has finite Lebesgue measure. -/
theorem win_window_ne_top {δ z : ℝ} :
    (MeasureTheory.volume {t : ℝ | |Real.log z - t| ≤ δ}) ≠ ⊤ := by
  rw [win_window_eq_Icc]
  exact (isCompact_Icc.measure_lt_top).ne

/-! ## The elementary bound on the majorant -/

/-- The squared majorant `(|a| + √b · √(π/4))²` is dominated by `2 M² + 2 b` as soon as
`|a| ≤ M` and `0 ≤ b`: expand the square, use `√b² = b`, and `√(π/4)² = π/4 ≤ 1`. -/
theorem sq_majorant_le (a b M : ℝ) (ha : |a| ≤ M) (hb : 0 ≤ b) :
    (|a| + Real.sqrt b * Real.sqrt (Real.pi / 4)) ^ 2 ≤ 2 * M ^ 2 + 2 * b := by
  have h1 : (|a| + Real.sqrt b * Real.sqrt (Real.pi / 4)) ^ 2
      ≤ 2 * |a| ^ 2 + 2 * (Real.sqrt b * Real.sqrt (Real.pi / 4)) ^ 2 := by
    nlinarith [sq_nonneg (|a| - Real.sqrt b * Real.sqrt (Real.pi / 4))]
  have h2 : 2 * |a| ^ 2 ≤ 2 * M ^ 2 := by nlinarith [ha, abs_nonneg a]
  have h3 : 2 * (Real.sqrt b * Real.sqrt (Real.pi / 4)) ^ 2 ≤ 2 * b := by
    have h := Real.sq_sqrt hb
    rw [mul_pow, h, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi / 4)]
    nlinarith [Real.pi_lt_four, hb]
  linarith

/-! ## The majorant is integrable along the logarithmic window -/

/-- **Integrability of the windowed slice majorant.**  For a trace-class datum `G`, the
pointwise majorant `thSliceMajorant G (exp t)` of the angular derivative of the slice at radius
`exp t` is integrable on the logarithmic window `|log z - t| ≤ δ`.

The window is compact, so the landmark value `|∂_θG(exp t, π/4)|` is bounded on it (the datum is
`C^∞` on the open quadrant), while the slice energy
`∫_θ (∂_θ²G(exp t, θ))² σ_η θ` is window-integrable by `window_ttIntS_integrable`; the majorant
is dominated by `2M² + 2·(slice energy)` there. -/
theorem win_majorant_integrable (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ z : ℝ) (hδ : 0 < δ) (hz : 0 < z) :
    MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ
        then Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G (Real.exp t) else 0) := by
  -- ## the window is measurable and of finite measure
  have hWmeas : MeasurableSet {t : ℝ | |Real.log z - t| ≤ δ} :=
    measurableSet_le (continuous_abs.comp (continuous_const.sub continuous_id)).measurable
      measurable_const
  have hWtop : (MeasureTheory.volume {t : ℝ | |Real.log z - t| ≤ δ}) ≠ ⊤ :=
    win_window_ne_top
  -- ## the slice energy is nonnegative and, windowed, integrable
  have hBnn : ∀ t : ℝ, 0 ≤ (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) := by
    intro t
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hBint : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) else 0) :=
    (window_ttIntS_integrable G hT hF δ z hδ hz).2
  -- ## the landmark value is continuous along `t ↦ exp t`, hence bounded on the window
  have hAcont : Continuous (fun t : ℝ => Work.Spaces.pth G (Real.exp t) (Real.pi / 4)) := by
    have hq0 : (0 : ℝ) < Real.pi / 4 := by positivity
    have hq1 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
    have hmap : Continuous (fun t : ℝ => (Real.exp t, Real.pi / 4)) :=
      Real.continuous_exp.prodMk continuous_const
    exact (hT.1.pth).continuousOn.comp_continuous hmap (fun t => ⟨Real.exp_pos t, hq0, hq1⟩)
  obtain ⟨M, hM0, hAM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |Real.log z - t| ≤ δ →
      |Work.Spaces.pth G (Real.exp t) (Real.pi / 4)| ≤ M := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hAcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (Real.log z - δ) (Real.log z + δ) := by
      rw [← win_window_eq_Icc]
      exact ht
    rw [← Real.norm_eq_abs]
    exact le_trans (hC t ht') (le_max_left _ _)
  -- ## the integrable majorant `2M² + 2·(slice energy)`
  have hmaj1 : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then 2 * M ^ 2 else 0) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff (f := fun _ : ℝ => 2 * M ^ 2) hWmeas).mpr
      (MeasureTheory.integrableOn_const hWtop)
  have hmaj2 : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) else 0) MeasureTheory.volume := by
    refine (hBint.const_mul 2).congr (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : |Real.log z - t| ≤ δ <;> simp [ht]
  have hmaj : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then 2 * M ^ 2 + 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) else 0) MeasureTheory.volume := by
    refine (hmaj1.add hmaj2).congr (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : |Real.log z - t| ≤ δ <;> simp [ht]
  -- ## the target function, written with the two windowed factors
  have htarget : ∀ t : ℝ,
      (if |Real.log z - t| ≤ δ
          then Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G (Real.exp t) else 0)
        = ((if |Real.log z - t| ≤ δ
              then |Work.Spaces.pth G (Real.exp t) (Real.pi / 4)| else 0)
            + Real.sqrt (if |Real.log z - t| ≤ δ then (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) else 0)
              * Real.sqrt (Real.pi / 4)) ^ 2 := by
    intro t
    by_cases ht : |Real.log z - t| ≤ δ
    · rw [if_pos ht, if_pos ht, if_pos ht]
      rfl
    · rw [if_neg ht, if_neg ht, if_neg ht, Real.sqrt_zero, zero_mul, add_zero, sq, mul_zero]
  -- ## a.e. strong measurability of the target
  have htarget_aesm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ
        then Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G (Real.exp t) else 0)
      MeasureTheory.volume := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
        ((if |Real.log z - t| ≤ δ
              then |Work.Spaces.pth G (Real.exp t) (Real.pi / 4)| else 0)
            + Real.sqrt (if |Real.log z - t| ≤ δ then (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) else 0)
              * Real.sqrt (Real.pi / 4)) ^ 2) MeasureTheory.volume :=
      ((hAcont.abs.aestronglyMeasurable.indicator hWmeas).add
        ((Real.continuous_sqrt.comp_aestronglyMeasurable hBint.aestronglyMeasurable).mul
          aestronglyMeasurable_const)).pow 2
    refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
    exact (htarget t).symm
  -- ## pointwise domination by the majorant
  refine MeasureTheory.Integrable.mono' hmaj htarget_aesm ?_
  filter_upwards with t
  by_cases ht : |Real.log z - t| ≤ δ
  · rw [if_pos ht, if_pos ht, Real.norm_of_nonneg (thSliceMajorant_nonneg G (Real.exp t))]
    have h1 : Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G (Real.exp t)
        = (|Work.Spaces.pth G (Real.exp t) (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4)) ^ 2 := rfl
    rw [h1]
    exact sq_majorant_le _ _ M (hAM t ht) (hBnn t)
  · rw [if_neg ht, if_neg ht]
    simp

end Work.FTS.EllSol.EllPkgAux.MollDom

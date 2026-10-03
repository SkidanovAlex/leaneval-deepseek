import Mathlib
import Submission.Work.Pert.PinLogDev.Helpers
import Submission.Work.Pert.PinLogDev.axis_good_transport
import Submission.Work.Pert.PinLogDev.axis_dev_pointwise
import Submission.Work.Pert.PinLogDev.axis_integral_le
import Submission.Work.Pert.PinAux.Defs

/-!
# `Work.Pert.PinLogDev.axis_good_transport_eps`

The `ε`-relaxed companion of `Work.Pert.PinLogDev.axis_good_transport`: the same transport along
the axis-like line `s ↦ s • w`, `w = ±I`, away from the pinch, but with the defect decay
hypothesis carrying a *uniform additive* error `ε`,

  `‖F (s • w) - (s • w + 1)‖ ≤ Kd / s + ε` for `s ∈ [a,b]`,

and the conclusion carrying the corresponding integral `(32/31) (Kd log (b/a) + ε (b-a))`
(note `∫_a^b ε ds = ε (b-a)`, *not* `ε · b log (b/a)`).

The pointwise derivative estimate is `Helpers.deriv_le_of_clear` (Lemma A.2.4) and the interval
bookkeeping is the elementary `axis_integral_le_eps` below.
-/

namespace Work.Pert.PinLogDev

open Complex Metric MeasureTheory
open scoped Topology

noncomputable section

/-- `ε`-version of `Work.Pert.PinLogDev.axis_integral_le`: the sole difference is the constant
integrand `(32/31) ε`, whose integral is `(32/31) ε (b-a)`.  Both sides are in fact equal. -/
theorem axis_integral_le_eps {Cα M Kd C₂ Ξ a b ε : ℝ}
    (hCα : 0 < Cα) (hKd : 0 ≤ Kd) (hC₂ : 0 ≤ C₂) (hε : 0 ≤ ε)
    (ha : 0 < a) (hΞa : Ξ < a) (hab : a ≤ b) :
    (∫ s in a..b, (Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))
        + ((32 : ℝ) / 31) * (Kd * (1 / s) + ε)))
      ≤ Real.sqrt 2 * C₂ * (Real.log ((b - Ξ) / (a - Ξ))
          + ∫ s in a..b, (1 : ℝ) / (Cα + |s - M|))
        + ((32 : ℝ) / 31) * (Kd * Real.log (b / a) + ε * (b - a)) := by
  have hI1 : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / (Cα + |s - M|)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun s _ => by positivity)
  have hI2 : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / (s - Ξ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.div₀ continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun s hs => ne_of_gt (by have := hs.1; linarith))
  have hI3 : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.div₀ continuousOn_const continuousOn_id
      (fun s hs => ne_of_gt (by have := hs.1; linarith))
  have hI12 : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / (Cα + |s - M|) + 1 / (s - Ξ))
      volume a b := hI1.add hI2
  have hFa : IntervalIntegrable
      (fun s : ℝ => Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))) volume a b :=
    hI12.const_mul _
  have hKdI : IntervalIntegrable (fun s : ℝ => Kd * (1 / s)) volume a b := hI3.const_mul Kd
  have hKI : IntervalIntegrable (fun s : ℝ => Kd * (1 / s) + ε) volume a b :=
    hKdI.add intervalIntegrable_const
  have hFb : IntervalIntegrable (fun s : ℝ => ((32 : ℝ) / 31) * (Kd * (1 / s) + ε))
      volume a b := hKI.const_mul _
  have hAval : (∫ s in a..b, Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ)))
      = Real.sqrt 2 * C₂ * (Real.log ((b - Ξ) / (a - Ξ))
          + ∫ s in a..b, (1 : ℝ) / (Cα + |s - M|)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hI1 hI2,
      integral_one_div_sub hΞa hab]
    ring
  have hBval : (∫ s in a..b, ((32 : ℝ) / 31) * (Kd * (1 / s) + ε))
      = ((32 : ℝ) / 31) * (Kd * Real.log (b / a) + ε * (b - a)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hKdI
      intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_one_div_self ha hab,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have heq : (∫ s in a..b, (Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))
        + ((32 : ℝ) / 31) * (Kd * (1 / s) + ε)))
      = Real.sqrt 2 * C₂ * (Real.log ((b - Ξ) / (a - Ξ))
          + ∫ s in a..b, (1 : ℝ) / (Cα + |s - M|))
        + ((32 : ℝ) / 31) * (Kd * Real.log (b / a) + ε * (b - a)) := by
    rw [intervalIntegral.integral_add hFa hFb, hAval, hBval]
  exact le_of_eq heq

set_option maxHeartbeats 2000000 in
theorem axis_good_transport_eps
    {Ξ Rde C₂ Kd Cα M δ₀ Y₀ a b ε : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {w : ℂ}
    (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂) (hKd : 0 ≤ Kd) (hε0 : 0 ≤ ε)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hw : w = Complex.I ∨ w = -Complex.I)
    (hCα : Cα = (1 / α).re - Ξ) (hM : M = -(w.im) * (1 / α).im)
    (hδ : δ₀ = Real.sqrt 2 * Rde - Cα)
    (hCα0 : 0 < Cα) (hΞ0 : 0 < Ξ) (hY0 : 0 < Y₀)
    (hYde : Real.sqrt 2 * Rde ≤ Y₀ - Ξ)
    (ha : Y₀ ≤ a) (hab : a ≤ b)
    (hgood : ∀ s ∈ Set.Icc a b, δ₀ ≤ |s - M|)
    (hdec : ∀ s ∈ Set.Icc a b, ‖F ((s : ℂ) * w) - ((s : ℂ) * w + 1)‖ ≤ Kd / s + ε) :
    ‖Work.Pert.PinAux.Dev Φ ((b : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((a : ℂ) * w)‖ ≤
      Real.sqrt 2 * C₂ * (Real.log ((b - Ξ) / (a - Ξ))
          + ∫ s in a..b, (1 : ℝ) / (Cα + |s - M|))
        + (32 / 31) * (Kd * Real.log (b / a) + ε * (b - a)) := by
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hΞY0 : Ξ < Y₀ := by
    have := mul_pos h2pos hRde
    linarith
  have hapos : 0 < a := lt_of_lt_of_le hY0 ha
  have haΞ : Ξ < a := lt_of_lt_of_le hΞY0 ha
  -- the two margin identities at `s • w`
  have hA : ∀ s : ℝ, Work.Pert.margA Ξ α ((s : ℂ) * w) = Cα + |s - M| := by
    intro s
    rw [Work.Pert.PinLogDev.margA_axis_w hw s, hCα, hM]
  have hB : ∀ s : ℝ, 0 ≤ s → Work.Pert.margB Ξ α ((s : ℂ) * w) = s - Ξ :=
    fun s hs => Work.Pert.PinLogDev.margB_axis_w hw hs
  have hw1 : ‖w‖ = 1 := Work.Pert.PinLogDev.norm_axis_w hw
  -- pointwise derivative estimate on the interval
  have hpt : ∀ s ∈ Set.Icc a b,
      ‖deriv Φ ((s : ℂ) * w) - 1‖ ≤
        Real.sqrt 2 * C₂ / min (Cα + |s - M|) (s - Ξ) + (32 / 31) * (Kd / s + ε) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hY0 (le_trans ha hs.1)
    have hmargA : Work.Pert.margA Ξ α ((s : ℂ) * w) = Cα + |s - M| := hA s
    have hmargB : Work.Pert.margB Ξ α ((s : ℂ) * w) = s - Ξ := hB s (le_of_lt hs0)
    have hclear : Real.sqrt 2 * Rde ≤
        min (Work.Pert.margA Ξ α ((s : ℂ) * w)) (Work.Pert.margB Ξ α ((s : ℂ) * w)) := by
      rw [hmargA, hmargB]
      apply le_min
      · have hg := hgood s hs
        linarith [hδ, hg]
      · linarith [hYde, ha, hs.1]
    have hmain := deriv_le_of_clear (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (α := α)
      (F := F) (Φ := Φ) (z := (s : ℂ) * w) hRde hDE hNT hΦ hclear
    rw [hmargA, hmargB] at hmain
    refine le_trans hmain ?_
    have hd := hdec s hs
    have h32 : (0 : ℝ) ≤ 32 / 31 := by norm_num
    have := mul_le_mul_of_nonneg_left hd h32
    linarith
  -- the integrand of the transport bound
  have hbound : ∀ s ∈ Set.Icc a b, ‖deriv Φ ((s : ℂ) * w) - 1‖ ≤
      Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))
        + ((32 : ℝ) / 31) * (Kd * (1 / s) + ε) := by
    intro s hs
    have hApos : 0 < Cα + |s - M| := by have := abs_nonneg (s - M); linarith
    have hBpos : 0 < s - Ξ := by linarith [hs.1]
    refine le_trans (hpt s hs) ?_
    have hmin : 1 / min (Cα + |s - M|) (s - Ξ) ≤ 1 / (Cα + |s - M|) + 1 / (s - Ξ) := by
      rcases le_total (Cα + |s - M|) (s - Ξ) with h | h
      · rw [min_eq_left h]
        have : 0 < 1 / (s - Ξ) := by positivity
        linarith
      · rw [min_eq_right h]
        have : 0 < 1 / (Cα + |s - M|) := by positivity
        linarith
    have hmul : Real.sqrt 2 * C₂ * (1 / min (Cα + |s - M|) (s - Ξ))
        ≤ Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ)) :=
      mul_le_mul_of_nonneg_left hmin (by positivity)
    have h1 : Real.sqrt 2 * C₂ / min (Cα + |s - M|) (s - Ξ)
        = Real.sqrt 2 * C₂ * (1 / min (Cα + |s - M|) (s - Ξ)) := div_eq_mul_one_div _ _
    have h2 : (32 / 31) * (Kd / s + ε) = ((32 : ℝ) / 31) * (Kd * (1 / s) + ε) := by ring
    rw [h1, h2]
    exact add_le_add hmul le_rfl
  -- continuity of the integrand
  have hgcont : ContinuousOn (fun s : ℝ =>
      Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))
        + ((32 : ℝ) / 31) * (Kd * (1 / s) + ε)) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s : ℝ => 1 / (Cα + |s - M|)) (Set.Icc a b) := by
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact ((continuous_const.add
          (continuous_abs.comp (continuous_id.sub continuous_const))).continuousOn)
      · intro s _
        exact ne_of_gt (by have := abs_nonneg (s - M); linarith)
    have h2 : ContinuousOn (fun s : ℝ => 1 / (s - Ξ)) (Set.Icc a b) := by
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact (continuousOn_id.sub continuousOn_const)
      · intro s hs
        exact ne_of_gt (by linarith [hs.1] : 0 < s - Ξ)
    have h3 : ContinuousOn (fun s : ℝ => 1 / s) (Set.Icc a b) := by
      refine ContinuousOn.div continuousOn_const continuousOn_id ?_
      intro s hs
      exact ne_of_gt (by linarith [hs.1] : 0 < s)
    have h4 : ContinuousOn (fun s : ℝ => Kd * (1 / s) + ε) (Set.Icc a b) :=
      (continuousOn_const.mul h3).add continuousOn_const
    exact (continuousOn_const.mul (h1.add h2)).add (continuousOn_const.mul h4)
  -- differentiability of `Φ` along the segment
  have hdiff : ∀ s ∈ Set.Icc a b, DifferentiableAt ℂ Φ ((s : ℂ) * w) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans (le_of_lt hapos) hs.1
    have hmem : ((s : ℂ) * w) ∈ Work.Pert.Qm Ξ α := by
      rw [Work.Pert.mem_Qm_iff_marg, hA s, hB s hs0]
      exact ⟨by have := abs_nonneg (s - M); linarith, by linarith [hs.1, haΞ]⟩
    exact (hΦ.1 _ hmem).differentiableAt ((Work.Pert.isOpen_Qm_ Ξ α).mem_nhds hmem)
  -- fundamental theorem of calculus along the segment
  have hdev := Work.Pert.PinLogDev.axis_dev_le hw1 hab hdiff hbound hgcont
  -- the integral comparison
  have hint := axis_integral_le_eps
    (Cα := Cα) (M := M) (Kd := Kd) (C₂ := C₂) (Ξ := Ξ) (a := a) (b := b) (ε := ε)
    hCα0 hKd hC₂ hε0 hapos haΞ hab
  simp only [Work.Pert.PinAux.Dev]
  exact le_trans hdev hint

end

end Work.Pert.PinLogDev

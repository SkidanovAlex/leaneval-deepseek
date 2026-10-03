import Mathlib
import Submission.Work.Pert.PinLogDev.Helpers
import Submission.Work.Pert.PinLogDev.axis_integral_le
import Submission.Work.Pert.PinLogDev.axis_dev_pointwise

/-!
# `Work.Pert.PinLogDev.axis_good_transport`

Transport of the deviation `Dev Φ = Φ - id` of a Fatou coordinate along the *axis-like* line
`s ↦ s • w`, `w = ± I`, `s ∈ [a,b]`, **away from the pinch** (`δ₀ ≤ |s - M|` on the interval).

The two margins of the gate `Qm Ξ α` at `s • w` are

* `margA = Cα + |s - M|` (the `A`-cone reaches height `M` at the axis), and
* `margB = s - Ξ`,

so the clearance is `min (Cα + |s-M|) (s - Ξ) / √2`, and the pointwise derivative estimate
(`Work.Pert.Pin3.dev_deriv_le_pt`, packaged as `Helpers.deriv_le_of_clear`) gives

  `‖dev_deriv Φ (s • w)‖ ≤ √2 C₂ / min (Cα + |s-M|) (s-Ξ) + (32/31)‖F (s • w) - (s • w + 1)‖`,

with `‖F (s • w) - (s • w + 1)‖ ≤ Kd / s` by hypothesis.  Integrating along the segment
(`Helpers.axis_dev_le`) and using `1 / min A B ≤ 1/A + 1/B`, this yields

  `‖Dev Φ (b • w) - Dev Φ (a • w)‖ ≤ √2 C₂ (∫ 1/(Cα + |s-M|) + ∫ 1/(s-Ξ)) + (32/31) Kd ∫ 1/s`,

and the two elementary integrals `∫_a^b ds/(s-Ξ) = log((b-Ξ)/(a-Ξ))`, `∫_a^b ds/s = log(b/a)`
(`Helpers.integral_one_div_sub`, `Helpers.integral_one_div_self`) give the claim.
-/

namespace Work.Pert.PinLogDev

open Complex Metric MeasureTheory
open scoped Topology

noncomputable section

set_option maxHeartbeats 2000000 in
theorem axis_good_transport
    {Ξ Rde C₂ Kd Cα M δ₀ Y₀ a b : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {w : ℂ}
    (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂) (hKd : 0 ≤ Kd)
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
    (hdec : ∀ s ∈ Set.Icc a b, ‖F ((s : ℂ) * w) - ((s : ℂ) * w + 1)‖ ≤ Kd / s) :
    ‖Work.Pert.PinAux.Dev Φ ((b : ℂ) * w) - Work.Pert.PinAux.Dev Φ ((a : ℂ) * w)‖ ≤
      Real.sqrt 2 * C₂ * (Real.log ((b - Ξ) / (a - Ξ))
          + ∫ s in a..b, (1 : ℝ) / (Cα + |s - M|))
        + (32 / 31) * Kd * Real.log (b / a) := by
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
  -- pointwise derivative estimate on the interval (`Work.Pert.PinLogDev.axis_dev_pointwise`)
  have hpt : ∀ s ∈ Set.Icc a b,
      ‖deriv Φ ((s : ℂ) * w) - 1‖ ≤
        Real.sqrt 2 * C₂ / min (Cα + |s - M|) (s - Ξ) + (32 / 31) * (Kd / s) :=
    Work.Pert.PinLogDev.axis_dev_pointwise
      (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (Kd := Kd) (Cα := Cα) (M := M) (δ₀ := δ₀)
      (Y₀ := Y₀) (a := a) (b := b) (α := α) (F := F) (Φ := Φ) (w := w)
      hRde hC₂ hKd hDE hNT hΦ hw hCα hM hδ hCα0 hΞ0 hY0 hYde ha hab hgood hdec
  -- the integrand of the transport bound
  have hbound : ∀ s ∈ Set.Icc a b, ‖deriv Φ ((s : ℂ) * w) - 1‖ ≤
      Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ)) + ((32 : ℝ) / 31) * Kd * (1 / s) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans (le_of_lt hapos) hs.1
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
    have h2 : (32 / 31) * (Kd / s) = ((32 : ℝ) / 31) * Kd * (1 / s) := by ring
    rw [h1, h2]
    exact add_le_add hmul le_rfl
  -- continuity of the integrand
  have hgcont : ContinuousOn (fun s : ℝ =>
      Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))
        + ((32 : ℝ) / 31) * Kd * (1 / s)) (Set.Icc a b) := by
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
    exact (continuousOn_const.mul (h1.add h2)).add (continuousOn_const.mul h3)
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
  -- the integral comparison (`Work.Pert.PinLogDev.axis_integral_le`)
  have hint := Work.Pert.PinLogDev.axis_integral_le
    (Cα := Cα) (M := M) (Kd := Kd) (C₂ := C₂) (Ξ := Ξ) (a := a) (b := b)
    hCα0 hKd hC₂ hapos haΞ hab
  simp only [Work.Pert.PinAux.Dev]
  exact le_trans hdev hint

end

end Work.Pert.PinLogDev

import Mathlib
import Submission.Work.Pert.PinLogDev.Helpers

namespace Work.Pert.PinLogDev

theorem axis_dev_pointwise
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
    ∀ s ∈ Set.Icc a b,
      ‖deriv Φ ((s : ℂ) * w) - 1‖ ≤
        Real.sqrt 2 * C₂ / min (Cα + |s - M|) (s - Ξ) + (32 / 31) * (Kd / s) := by
  intro s hs
  -- `s ≥ a ≥ Y₀ > 0`, so the axis point `s • w` has nonnegative parameter.
  have hs0 : 0 < s := lt_of_lt_of_le hY0 (le_trans ha hs.1)
  -- Evaluate the two gate margins at `s • w` (`w = ±I`).
  have hmargA : Work.Pert.margA Ξ α ((s : ℂ) * w) = Cα + |s - M| := by
    rw [margA_axis_w hw s, hCα, hM]
  have hmargB : Work.Pert.margB Ξ α ((s : ℂ) * w) = s - Ξ :=
    margB_axis_w hw (le_of_lt hs0)
  -- The clearance hypothesis of the pointwise derivative estimate.
  have hclear : Real.sqrt 2 * Rde ≤
      min (Work.Pert.margA Ξ α ((s : ℂ) * w)) (Work.Pert.margB Ξ α ((s : ℂ) * w)) := by
    rw [hmargA, hmargB]
    apply le_min
    · have hg := hgood s hs
      linarith [hδ, hg]
    · linarith [hYde, ha, hs.1]
  -- Pointwise derivative bound (Lemma A.2.4) at `s • w`.
  have hmain := deriv_le_of_clear (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (α := α)
    (F := F) (Φ := Φ) (z := (s : ℂ) * w) hRde hDE hNT hΦ hclear
  rw [hmargA, hmargB] at hmain
  refine le_trans hmain ?_
  -- Replace the defect by the decay hypothesis `‖F z - (z+1)‖ ≤ Kd/s`.
  have hd := hdec s hs
  have h32 : (0 : ℝ) ≤ 32 / 31 := by norm_num
  have := mul_le_mul_of_nonneg_left hd h32
  linarith

end Work.Pert.PinLogDev

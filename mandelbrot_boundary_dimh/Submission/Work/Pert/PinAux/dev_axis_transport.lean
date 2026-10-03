import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.PinAux.Basic
import Submission.Work.Pert.PinAux.collar_to_medial
import Submission.Work.Pert.PinAux.medial_to_axis

namespace Work.Pert.PinAux

open MandelDim Complex Metric MeasureTheory

noncomputable section

/-!
# `Work.Pert.PinAux.dev_axis_transport`

Transport of the deviation `Dev := Φ - id` of a Fatou coordinate `Φ` on the gate `Qm Ξ α`
from a point `z` of the gate (whose `R₁`-ball lies in the gate) to the two axis points `± i T`.

The two ingredients are proved in their own files (they import the definitions from
`Submission.Work.Pert.PinAux.Basic`):

* `Work.Pert.PinAux.collar_to_medial` — the deviation from `z` to the *medial* point of its
  slice is `≤ Λ (1 + log (2+‖z‖)) + (c/(1-c)) (‖z - med‖ + 1)`;
* `Work.Pert.PinAux.medial_to_axis` — the medial value is transported to `± i T` for a suitable
  `T ∈ [Y₀, Y₀+1]` with `Λ ≤ 2 c/(1-c)`.

The elementary lemmas `arith_lin` (linear bookkeeping) and `arith_absorb` (logarithmic
absorption of the constant) combine the two, the budget being `3 c/(1-c) ≤ 1/64`, which holds
because `c ≤ 1/256`.
-/

/-- **The transport of the deviation to the axis.**  For every point `z` of the gate whose
`R₁`-ball lies in the gate there is `T ≥ Y₀` (indeed `T ∈ [Y₀, Y₀+1]`) making the deviation
`Dev z = Φ z - z` comparable with the deviations at `± i T`, with the logarithmic bound and
the linear slack `‖z‖/64` of the statement. -/
theorem dev_axis_transport {F Φ : ℂ → ℂ} {α : ℂ} {Ξ c Y₀ R₁ : ℝ}
    (hΞ : 0 < Ξ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256) (hY₀ : 0 < Y₀) (hR₁ : 0 < R₁)
    (hDE : MandelDim.FatouDerivEstimate)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hsharp : ∃ K : ℝ, 0 < K ∧ ∀ w ∈ Work.Pert.Qm Ξ α,
      ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α →
      Metric.ball z R₁ ⊆ Work.Pert.Qm Ξ α →
      ∃ T : ℝ, Y₀ ≤ T ∧
        (‖(Φ z - z) - (Φ (T * Complex.I) - T * Complex.I)‖
            ≤ C * (1 + Real.log (2 + ‖z‖)) + ‖z‖ / 64 ∧
         ‖(Φ z - z) - (Φ (-(T * Complex.I)) + T * Complex.I)‖
            ≤ C * (1 + Real.log (2 + ‖z‖)) + ‖z‖ / 64) := by
  obtain ⟨ΛA, hΛApos, hA⟩ := collar_to_medial hΞ hc0 hc hY₀ hR₁ hDE hNT hΦ hsharp
  obtain ⟨CB, ΛB, hCBpos, hΛB0, hΛBle, hB⟩ := medial_to_axis hΞ hc0 hc hY₀ hR₁ hDE hNT hΦ hsharp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrate0 : 0 ≤ c / (1 - c) := div_nonneg hc0 (by linarith)
  have hM0 : 0 ≤ max (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0 := le_max_right _ _
  have hY02 : 0 ≤ Y₀ + 2 := by linarith
  have hKnn : 0 ≤ (c / (1 - c)) * (max (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0 + 1)
      + (2 * (c / (1 - c))) * (Y₀ + 2) := by
    have h1 : 0 ≤ max (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0 + 1 := by linarith
    have h2 : 0 ≤ 2 * (c / (1 - c)) := by linarith
    nlinarith [hrate0, h1, h2]
  obtain ⟨C, hCpos, hCab⟩ := arith_absorb (ΛA := ΛA) (CB := CB)
    (K := (c / (1 - c)) * (max (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0 + 1)
      + (2 * (c / (1 - c))) * (Y₀ + 2)) hΛApos hCBpos hKnn hlog2
  refine ⟨C, hCpos, ?_⟩
  intro z hz hball
  obtain ⟨T, hT0, hT1, hcmp1, hcmp2⟩ := hB z hz hball
  have hAz := hA z hz hball
  have hgeo : ‖z - med Ξ α z.im‖ ≤ ‖z‖ + max (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0 := by
    calc ‖z - med Ξ α z.im‖ ≤ width Ξ α z.im / 2 :=
          norm_sub_med_le (Ξ := Ξ) (α := α) (z := z) hz
      _ ≤ |z.im| + (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) := width_div_two_le Ξ α z.im
      _ ≤ ‖z‖ + max (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0 := by
          have hmax := le_max_left (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0
          have him := Complex.abs_im_le_norm z
          linarith
  have hTabs : |T| = T := abs_of_nonneg (by linarith [hY₀, hT0])
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hdT1 : |z.im - T| ≤ ‖z‖ + (Y₀ + 1) := by
    have h5 : |z.im - T| ≤ |z.im| + |T| := by
      have h6 : |z.im - T| ≤ |z.im| + |-T| := abs_add_le _ _
      rwa [abs_neg] at h6
    rw [hTabs] at h5; linarith
  have hdT2 : |z.im + T| ≤ ‖z‖ + (Y₀ + 1) := by
    have h5 : |z.im + T| ≤ |z.im| + |T| := abs_add_le _ _
    rw [hTabs] at h5; linarith
  have hlin1 := arith_lin (c := c) (ΛB := ΛB) (y := ‖z‖) (ℓ := ‖z - med Ξ α z.im‖)
    (dd := z.im - T) (M := max (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0) (Y₀ := Y₀)
    hc0 hc hΛB0 hΛBle hgeo hdT1
  have hlin2 := arith_lin (c := c) (ΛB := ΛB) (y := ‖z‖) (ℓ := ‖z - med Ξ α z.im‖)
    (dd := z.im + T) (M := max (((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2) 0) (Y₀ := Y₀)
    hc0 hc hΛB0 hΛBle hgeo hdT2
  have hL : 1 + Real.log 2 ≤ 1 + Real.log (2 + ‖z‖) := by
    have h2 : (2 : ℝ) ≤ 2 + ‖z‖ := by linarith [norm_nonneg z]
    have h3 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
    linarith
  have habs := hCab (1 + Real.log (2 + ‖z‖)) hL
  have hrate : 3 * (c / (1 - c)) * ‖z‖ ≤ ‖z‖ / 64 := by
    have hc1 : 0 < 1 - c := by linarith
    have hr : 3 * (c / (1 - c)) ≤ 1 / 64 := by
      rw [show 3 * (c / (1 - c)) = 3 * c / (1 - c) by ring, div_le_iff₀ hc1]
      nlinarith
    have := mul_le_mul_of_nonneg_right hr (norm_nonneg z); linarith
  have hsplit1 : ‖Dev Φ z - Dev Φ ((T : ℂ) * Complex.I)‖
      ≤ ‖Dev Φ z - Dev Φ (med Ξ α z.im)‖ + ‖Dev Φ (med Ξ α z.im) - Dev Φ ((T : ℂ) * Complex.I)‖ := by
    have he : Dev Φ z - Dev Φ ((T : ℂ) * Complex.I)
        = (Dev Φ z - Dev Φ (med Ξ α z.im)) + (Dev Φ (med Ξ α z.im) - Dev Φ ((T : ℂ) * Complex.I)) := by
      ring
    rw [he]; exact norm_add_le _ _
  have hsplit2 : ‖Dev Φ z - Dev Φ (-(T * Complex.I))‖
      ≤ ‖Dev Φ z - Dev Φ (med Ξ α z.im)‖ + ‖Dev Φ (med Ξ α z.im) - Dev Φ (-(T * Complex.I))‖ := by
    have he : Dev Φ z - Dev Φ (-(T * Complex.I))
        = (Dev Φ z - Dev Φ (med Ξ α z.im)) + (Dev Φ (med Ξ α z.im) - Dev Φ (-(T * Complex.I))) := by
      ring
    rw [he]; exact norm_add_le _ _
  have hgoal1 : ‖(Φ z - z) - (Φ (T * Complex.I) - T * Complex.I)‖
      = ‖Dev Φ z - Dev Φ ((T : ℂ) * Complex.I)‖ := rfl
  have hgoal2 : ‖(Φ z - z) - (Φ (-(T * Complex.I)) + T * Complex.I)‖
      = ‖Dev Φ z - Dev Φ (-(T * Complex.I))‖ := by
    have he : Dev Φ (-(T * Complex.I)) = Φ (-(T * Complex.I)) + T * Complex.I := by
      simp only [Dev]; ring
    rw [he]
    rfl
  refine ⟨T, hT0, ?_, ?_⟩
  · rw [hgoal1]
    have hcomb : ‖Dev Φ z - Dev Φ ((T : ℂ) * Complex.I)‖
        ≤ (ΛA * (1 + Real.log (2 + ‖z‖)) + c / (1 - c) * (‖z - med Ξ α z.im‖ + 1))
          + (CB * (1 + Real.log (2 + ‖z‖)) + ΛB * (|z.im - T| + 1)) :=
      le_trans hsplit1 (add_le_add hAz hcmp1)
    nlinarith [hcomb, hlin1, habs, hrate]
  · rw [hgoal2]
    have hcomb : ‖Dev Φ z - Dev Φ (-(T * Complex.I))‖
        ≤ (ΛA * (1 + Real.log (2 + ‖z‖)) + c / (1 - c) * (‖z - med Ξ α z.im‖ + 1))
          + (CB * (1 + Real.log (2 + ‖z‖)) + ΛB * (|z.im + T| + 1)) :=
      le_trans hsplit2 (add_le_add hAz hcmp2)
    nlinarith [hcomb, hlin2, habs, hrate]

end

end Work.Pert.PinAux

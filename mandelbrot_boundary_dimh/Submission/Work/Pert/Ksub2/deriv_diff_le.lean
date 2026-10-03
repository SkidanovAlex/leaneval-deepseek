import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# `Work.Pert.Ksub2.deriv_diff_le`

Comparison of the derivatives of two (univalent) Fatou coordinates of two near-translations
`F`, `F₀` on a common ball of radius `R`, given Shishikura's derivative estimate
`MandelDim.FatouDerivEstimate` (Lemma A.2.4(i)).

Write `v = F - id` and `v₀ = F₀ - id`; the hypotheses `‖F w - (w+1)‖ < 1/4` say
`‖v w - 1‖ < 1/4` (and likewise for `v₀`), so `‖v w‖ > 3/4` and `‖v₀ w‖ > 3/4`.  A.2.4(i) gives
`‖deriv Φ z - 1/v z‖ ≤ C₂/R` and `‖deriv Φ₀ z - 1/v₀ z‖ ≤ C₂/R`, while the `C⁰` closeness
`‖F w - F₀ w‖ ≤ E` gives
`‖1/v z - 1/v₀ z‖ = ‖v₀ z - v z‖/(‖v z‖ ‖v₀ z‖) ≤ E/(9/16) = 16E/9 ≤ 4E`.
Triangle inequality then yields the claim with `C = max R₁ (max (2 C₂) 1)`.
-/

namespace Work.Pert.Ksub2

open scoped Topology
open Metric

theorem deriv_diff_le (hDE : MandelDim.FatouDerivEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F F₀ Φ Φ₀ : ℂ → ℂ} {R E : ℝ} {z : ℂ},
      C ≤ R → 0 ≤ E →
      DifferentiableOn ℂ F (Metric.ball z R) → DifferentiableOn ℂ F₀ (Metric.ball z R) →
      MandelDim.IsFatouCoordOn F Φ (Metric.ball z R) →
      MandelDim.IsFatouCoordOn F₀ Φ₀ (Metric.ball z R) →
      DifferentiableAt ℂ Φ z → DifferentiableAt ℂ Φ₀ z →
      (∀ w ∈ Metric.ball z R, ‖F w - (w + 1)‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, ‖F₀ w - (w + 1)‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, ‖F w - F₀ w‖ ≤ E) →
      ‖deriv Φ z - deriv Φ₀ z‖ ≤ C / R + 4 * E := by
  obtain ⟨R₁, C₁, C₂, hR₁, hC₁, hC₂, hEst⟩ := hDE
  refine ⟨max R₁ (max (2 * C₂) 1), ?_, ?_⟩
  · exact lt_max_iff.mpr (Or.inl hR₁)
  · intro F F₀ Φ Φ₀ R E z hCR hE hdF hdF₀ hΦ hΦ₀ _ _ hclose hclose₀ hnear
    have hR₁R : R₁ ≤ R := le_trans (le_max_left _ _) hCR
    have hCR' : (2 * C₂) ≤ max R₁ (max (2 * C₂) 1) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hRpos : 0 < R := lt_of_lt_of_le hR₁ hR₁R
    have hz : z ∈ Metric.ball z R := Metric.mem_ball_self hRpos
    set v : ℂ → ℂ := fun w => F w - w with hvdef
    set v₀ : ℂ → ℂ := fun w => F₀ w - w with hv₀def
    have hv_eq : v = F - id := by funext w; simp [hvdef]
    have hv₀_eq : v₀ = F₀ - id := by funext w; simp [hv₀def]
    have hdv : DifferentiableOn ℂ v (Metric.ball z R) := by
      rw [hv_eq]; exact hdF.sub differentiableOn_id
    have hdv₀ : DifferentiableOn ℂ v₀ (Metric.ball z R) := by
      rw [hv₀_eq]; exact hdF₀.sub differentiableOn_id
    have hv1 : ∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4 := by
      intro w hw
      simpa [hvdef, sub_sub] using hclose w hw
    have hv1₀ : ∀ w ∈ Metric.ball z R, ‖v₀ w - 1‖ < 1 / 4 := by
      intro w hw
      simpa [hv₀def, sub_sub] using hclose₀ w hw
    have hrelv : ∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1 := by
      intro w hw hw'
      have hthis : w + v w = F w := by simp [hvdef]
      rw [hthis]
      exact hΦ.2.2 w hw (hthis ▸ hw')
    have hrelv₀ : ∀ w ∈ Metric.ball z R, w + v₀ w ∈ Metric.ball z R → Φ₀ (w + v₀ w) = Φ₀ w + 1 := by
      intro w hw hw'
      have hthis : w + v₀ w = F₀ w := by simp [hv₀def]
      rw [hthis]
      exact hΦ₀.2.2 w hw (hthis ▸ hw')
    have hΦest : ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R :=
      (hEst Φ v z R hR₁R hΦ.1 hΦ.2.1 hdv hv1 hrelv).2
    have hΦ₀est : ‖deriv Φ₀ z - 1 / v₀ z‖ ≤ C₂ / R :=
      (hEst Φ₀ v₀ z R hR₁R hΦ₀.1 hΦ₀.2.1 hdv₀ hv1₀ hrelv₀).2
    have hv_ge : (3 : ℝ) / 4 < ‖v z‖ := by
      have h := hv1 z hz
      have h2 : |‖v z‖ - 1| ≤ ‖v z - 1‖ := by
        have := abs_norm_sub_norm_le (v z) (1 : ℂ)
        rwa [norm_one] at this
      have h3 : 1 - ‖v z‖ ≤ ‖v z - 1‖ := by
        have := neg_le_abs (‖v z‖ - 1); linarith
      linarith
    have hv₀_ge : (3 : ℝ) / 4 < ‖v₀ z‖ := by
      have h := hv1₀ z hz
      have h2 : |‖v₀ z‖ - 1| ≤ ‖v₀ z - 1‖ := by
        have := abs_norm_sub_norm_le (v₀ z) (1 : ℂ)
        rwa [norm_one] at this
      have h3 : 1 - ‖v₀ z‖ ≤ ‖v₀ z - 1‖ := by
        have := neg_le_abs (‖v₀ z‖ - 1); linarith
      linarith
    have hvz_ne : v z ≠ 0 := by
      intro h; rw [h] at hv_ge; simp only [norm_zero] at hv_ge; linarith
    have hv₀z_ne : v₀ z ≠ 0 := by
      intro h; rw [h] at hv₀_ge; simp only [norm_zero] at hv₀_ge; linarith
    have hden_pos : 0 < ‖v z‖ * ‖v₀ z‖ := mul_pos (by linarith) (by linarith)
    have hnum : ‖v₀ z - v z‖ ≤ E := by
      have h1 : v₀ z - v z = F₀ z - F z := by simp only [hvdef, hv₀def]; ring
      rw [h1, norm_sub_rev]
      exact hnear z hz
    have hden_ge : (9 : ℝ) / 16 ≤ ‖v z‖ * ‖v₀ z‖ := by
      have h1 : (3 : ℝ) / 4 ≤ ‖v z‖ := le_of_lt hv_ge
      have h2 : (3 : ℝ) / 4 ≤ ‖v₀ z‖ := le_of_lt hv₀_ge
      have h3 := mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 3/4) (by linarith)
      linarith
    have h_inv : ‖1 / v z - 1 / v₀ z‖ ≤ 16 / 9 * E := by
      have hkey : 1 / v z - 1 / v₀ z = (v₀ z - v z) / (v z * v₀ z) := by
        field_simp
      rw [hkey, norm_div, norm_mul]
      rw [div_le_iff₀ hden_pos]
      have h1 : (1 : ℝ) ≤ 16 / 9 * (‖v z‖ * ‖v₀ z‖) := by linarith
      have h2 : E ≤ 16 / 9 * E * (‖v z‖ * ‖v₀ z‖) := by
        have h3 := mul_le_mul_of_nonneg_left h1 hE
        nlinarith [h3]
      nlinarith [hnum, hE]
    calc ‖deriv Φ z - deriv Φ₀ z‖
        = ‖(deriv Φ z - 1 / v z) + (1 / v z - 1 / v₀ z) + (1 / v₀ z - deriv Φ₀ z)‖ := by
            congr 1; ring
      _ ≤ ‖deriv Φ z - 1 / v z‖ + ‖1 / v z - 1 / v₀ z‖ + ‖1 / v₀ z - deriv Φ₀ z‖ := by
            have h1 := norm_add_le ((deriv Φ z - 1 / v z) + (1 / v z - 1 / v₀ z))
              (1 / v₀ z - deriv Φ₀ z)
            have h2 := norm_add_le (deriv Φ z - 1 / v z) (1 / v z - 1 / v₀ z)
            linarith
      _ = ‖deriv Φ z - 1 / v z‖ + ‖1 / v z - 1 / v₀ z‖ + ‖deriv Φ₀ z - 1 / v₀ z‖ := by
            rw [norm_sub_rev (1 / v₀ z) (deriv Φ₀ z)]
      _ ≤ C₂ / R + 16 / 9 * E + C₂ / R := by linarith
      _ = 2 * C₂ / R + 16 / 9 * E := by ring
      _ ≤ max R₁ (max (2 * C₂) 1) / R + 4 * E := by
            have h1 : 2 * C₂ / R ≤ max R₁ (max (2 * C₂) 1) / R :=
              div_le_div_of_nonneg_right hCR' (le_of_lt hRpos)
            have h2 : (16 : ℝ) / 9 * E ≤ 4 * E :=
              mul_le_mul_of_nonneg_right (by norm_num : (16:ℝ)/9 ≤ 4) hE
            linarith

end Work.Pert.Ksub2

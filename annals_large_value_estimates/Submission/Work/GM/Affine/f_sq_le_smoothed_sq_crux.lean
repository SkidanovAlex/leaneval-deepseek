import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.f_sq_le_smoothed_sq_of_high_tail
import Submission.Work.GM.Affine.high_tail_le_low_sq

namespace Work.GM.Affine

/-- The `L²`-comparison `∫ f² ≤ C T^{2δ} ∫ f̃²` (`f̃ = smoothed psiSmooth T f`).

This is the assembly: the analytic input is the high-frequency tail bound
`high_tail_le_low_sq` (the positive tail of `‖Fhat f‖²` is dominated by the
middle range), and the measure-theoretic part is `f_sq_le_smoothed_sq_of_high_tail`,
which converts it into the stated `L²` comparison. -/
theorem f_sq_le_smoothed_sq_crux {C₀ T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∫ u, (f u) ^ 2 ≤ C * T ^ (2 * δ) * ∫ u, (smoothed psiSmooth T f u) ^ 2 := by
  obtain ⟨C, hCpos, hcrux⟩ := high_tail_le_low_sq hC₀ hT₀ c δ hδ
  exact f_sq_le_smoothed_sq_of_high_tail hC₀ hT₀ hδ hcrux

end Work.GM.Affine

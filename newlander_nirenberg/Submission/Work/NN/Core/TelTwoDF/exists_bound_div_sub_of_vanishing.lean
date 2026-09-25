import Mathlib

namespace Work.NN.Core.TelTwoDF

/-- **Boundedness of a quotient whose numerator vanishes near the pole.**

Let `ρ > 0`, let `ψ : ℂ → ℂ` be bounded (`∃ C, ∀ w, ‖ψ w‖ ≤ C`) and vanish on the open disc
`ball c ρ` (`∀ w, ‖w - c‖ < ρ → ψ w = 0`).  Then `w ↦ ψ w / (w - c)` is bounded:

  `∃ C, ∀ w, ‖ψ w / (w - c)‖ ≤ C`.

Route: for `‖w - c‖ < ρ` the numerator vanishes, so the quotient is `0`; otherwise
`‖ψ w / (w - c)‖ ≤ C₀ * ρ⁻¹` with `C₀` a bound on `‖ψ‖` (using `‖(w - c)⁻¹‖ ≤ ρ⁻¹`, which
requires `‖w - c‖ ≥ ρ > 0`).  The case `w = c` is covered by the first case
(`‖c - c‖ = 0 < ρ`); note `C₀ ≥ 0` follows from the bound, so `C₀ * ρ⁻¹` is the right shape. -/
theorem exists_bound_div_sub_of_vanishing {ψ : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hzero : ∀ w : ℂ, ‖w - c‖ < ρ → ψ w = 0) (hb : ∃ C, ∀ w : ℂ, ‖ψ w‖ ≤ C) :
    ∃ C, ∀ w : ℂ, ‖ψ w / (w - c)‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := hb
  have hC0nn : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0)
  refine ⟨C₀ * ρ⁻¹, fun w => ?_⟩
  rcases lt_or_ge (‖w - c‖) ρ with h | h
  · rw [hzero w h, zero_div, norm_zero]
    exact mul_nonneg hC0nn (inv_nonneg.mpr hρ.le)
  · have hpos : 0 < ‖w - c‖ := lt_of_lt_of_le hρ h
    rw [div_eq_mul_inv, norm_mul, norm_inv]
    have hle : ‖w - c‖⁻¹ ≤ ρ⁻¹ := (inv_le_inv₀ hpos hρ).mpr h
    exact mul_le_mul (hC₀ w) hle (inv_nonneg.mpr (norm_nonneg _)) hC0nn

end Work.NN.Core.TelTwoDF

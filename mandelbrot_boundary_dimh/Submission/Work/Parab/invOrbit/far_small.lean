import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.inversion.exists_norm_sub_le_of_asymptotic
import Submission.Work.Parab.invOrbit.norm_add_affine_log_eventually_gt

namespace Work.Parab.invOrbit

/-- **Far points have small image.**

If `φ` has an abelian-coordinate expansion `τ₀(φ w) = w + a log(-w) + b + o(1)` along a set `S`
of large `w`, then `φ w` is eventually small: `τ₀ = -1/(·)` is an involution, so `φ w` behaves
like `-1/w` along `S`.  Concretely, for `‖w‖` large,

`1/‖φ w‖ = ‖τ₀ (φ w)‖ ≥ ‖w + a log(-w) + b‖ - ε > 1/ρ`.

This is the "preimage of a far value is far" step of Shishikura, Lemma 5.1 (the asymptotic
expansion of the Fatou coordinate forces the inverse branch to converge to `0`). -/
theorem far_small {φ : ℂ → ℂ} {S : Set ℂ} {a b : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hasymp : ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ S, R < ‖w‖ →
        ‖MandelDim.tau0 (φ w) - (w + a * Complex.log (-w) + b)‖ < ε) :
    ∃ R : ℝ, ∀ w ∈ S, R < ‖w‖ → ‖φ w‖ < ρ := by
  have hρinv : 0 < ρ⁻¹ := inv_pos.mpr hρ
  obtain ⟨R₁, hR₁⟩ := hasymp ρ⁻¹ hρinv
  obtain ⟨R₂, hR₂⟩ :=
    norm_add_affine_log_eventually_gt (a := a) (b := b) (c := 2 * ρ⁻¹) (by positivity)
  refine ⟨max R₁ R₂, fun w hwS hw => ?_⟩
  have h1 : ‖MandelDim.tau0 (φ w) - (w + a * Complex.log (-w) + b)‖ < ρ⁻¹ :=
    hR₁ w hwS (lt_of_le_of_lt (le_max_left _ _) hw)
  have h2 : 2 * ρ⁻¹ < ‖w + a * Complex.log (-w) + b‖ :=
    hR₂ w (lt_of_le_of_lt (le_max_right _ _) hw)
  have h3 : ρ⁻¹ < ‖MandelDim.tau0 (φ w)‖ := by
    have h := abs_norm_sub_norm_le (MandelDim.tau0 (φ w)) (w + a * Complex.log (-w) + b)
    have h' : ‖w + a * Complex.log (-w) + b‖ - ‖MandelDim.tau0 (φ w)‖
        ≤ ‖MandelDim.tau0 (φ w) - (w + a * Complex.log (-w) + b)‖ := by
      rw [abs_sub_comm] at h
      exact le_trans (le_abs_self _) h
    linarith
  have h4 : ‖MandelDim.tau0 (φ w)‖ = 1 / ‖φ w‖ := by simp [MandelDim.tau0]
  have h5 : ρ⁻¹ < (‖φ w‖)⁻¹ := by
    have := h3
    rw [h4] at this
    simpa using this
  have h6 : 0 < (‖φ w‖)⁻¹ := lt_trans hρinv h5
  exact (inv_lt_inv₀ hρ (inv_pos.mp h6)).mp h5

end Work.Parab.invOrbit

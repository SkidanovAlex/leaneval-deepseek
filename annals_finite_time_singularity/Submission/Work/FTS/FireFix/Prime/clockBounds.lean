import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.RegPkgGal.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- **Uniform bounds on the clock and its first-order combinations.**  On the fake-time strip
`[0,S]` the amplitude `A` and the scaling `B` are bounded away from `0` and their derivatives are
bounded, so all four quantities appearing in the dynamic-rescaling chain rule —
`A⁻¹`, `A'/A²`, `B⁻¹`, `B'/B` — are uniformly bounded by a single constant

  `M = max (max a₀⁻¹ b₀⁻¹) (max (|a₂|/a₀²) (|b₂|/b₀))`,

where `a₀`/`b₀` are the positive lower bounds of `A`/`B` and `a₂`/`b₂` the bounds on
`|A'|`/`|B'|`.  This is the elementary input of the time-Hölder estimates for `∂_τω`. -/
theorem clockBounds {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |(A τ)⁻¹| ≤ M ∧ |deriv A τ / (A τ) ^ 2| ≤ M ∧ |(B τ)⁻¹| ≤ M ∧
        |deriv B τ / B τ| ≤ M := by
  obtain ⟨a₀, a₁, ha₀, ha⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hb⟩ := h.hBb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  obtain ⟨b₂, hb₂⟩ := h.hBd
  refine ⟨max (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀)), ?_, ?_⟩
  · have h1 : 0 ≤ a₀⁻¹ := inv_nonneg.mpr ha₀.le
    exact le_trans h1 (le_trans (le_max_left a₀⁻¹ b₀⁻¹)
      (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
  · intro τ hτ
    have hApos : 0 < A τ := h.hA τ hτ
    have hBpos : 0 < B τ := h.hB τ hτ
    have hAle : a₀ ≤ A τ := (ha τ hτ).1
    have hBle : b₀ ≤ B τ := (hb τ hτ).1
    have hP : |(A τ)⁻¹| ≤ a₀⁻¹ := by
      rw [abs_inv, abs_of_pos hApos, inv_le_inv₀ hApos ha₀]
      exact hAle
    have hQ : |(B τ)⁻¹| ≤ b₀⁻¹ := by
      rw [abs_inv, abs_of_pos hBpos, inv_le_inv₀ hBpos hb₀]
      exact hBle
    have hR : |deriv A τ / (A τ) ^ 2| ≤ |a₂| / a₀ ^ 2 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg (A τ))]
      exact div_le_div₀ (abs_nonneg a₂) (le_trans (ha₂ τ hτ) (le_abs_self a₂))
        (pow_pos ha₀ 2) (pow_le_pow_left₀ ha₀.le hAle 2)
    have hT : |deriv B τ / B τ| ≤ |b₂| / b₀ := by
      rw [abs_div, abs_of_pos hBpos]
      exact div_le_div₀ (abs_nonneg b₂) (le_trans (hb₂ τ hτ) (le_abs_self b₂)) hb₀ hBle
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_trans hP (le_trans (le_max_left a₀⁻¹ b₀⁻¹)
        (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hR (le_trans (le_max_left (|a₂| / a₀ ^ 2) (|b₂| / b₀))
        (le_max_right (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hQ (le_trans (le_max_right a₀⁻¹ b₀⁻¹)
        (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hT (le_trans (le_max_right (|a₂| / a₀ ^ 2) (|b₂| / b₀))
        (le_max_right (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))

end Work.FTS.FireFix.Prime

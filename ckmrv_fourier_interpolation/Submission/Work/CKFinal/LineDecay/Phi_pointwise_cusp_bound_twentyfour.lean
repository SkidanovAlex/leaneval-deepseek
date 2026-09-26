import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.Phi_axis_norm_twentyfour
import Submission.Work.CKFinal.LineDecay.KPlus_tail_lines_twentyfour
import Submission.Work.CKFinal.LineDecay.KMinus_tail_lines_twentyfour
import Submission.Work.CKFinal.LineDecay.DenomLower_lines

namespace Work.CKFinal.LineDecay

/-- **The pointwise cusp majorant for the second difference `Φ` in dimension 24.**

On the two lines `Re τ = ±1/2`, for `Im τ` large and `t ≥ 1`, the second differences of both
kernels are bounded by the same cusp majorant

`C (1+‖τ‖)^A · e^{-2π Im τ} · e^{-π t}/(1 + e^{2π(Im τ - t)})`.

Route: `Phi_axis_norm_twentyfour` gives `‖Φ(τ,t)‖ ≤ t^10 (‖K₊(τ,S·(it))‖ + ‖K₋(τ,S·(it))‖)`,
`KPlus_tail_lines_twentyfour`/`KMinus_tail_lines_twentyfour` bound each `t^10 ‖K_±‖` by the
displayed majorant (with their own exponents `A₊`, `A₋`), and `A := max A₊ A₋` together with
`(1+‖τ‖)^{A₊} ≤ (1+‖τ‖)^A` (as `1 + ‖τ‖ ≥ 1`) finishes. -/
theorem Phi_pointwise_cusp_bound_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im → 1 ≤ t →
        (‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 24) τ t‖
            ≤ C * (1 + ‖(τ : ℂ)‖) ^ A *
              (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))
          ∧ ‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 24) τ t‖
            ≤ C * (1 + ‖(τ : ℂ)‖) ^ A *
              (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))) := by
  -- The divisor lower bound on the two lines.
  obtain ⟨c, Yc, hc, hYc, hD⟩ := DenomLower_lines
  set Y : ℝ := max Yc 2 with hYdef
  have hY1 : 1 ≤ Y := le_trans hYc (le_max_left Yc 2)
  have hY2 : 2 ≤ Y := le_max_right Yc 2
  have hD' : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im → 1 ≤ t →
      c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
        ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
            (Work.Kernels.jInvariantFun τ
              - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ :=
    fun τ t ht hre hYτ ht1 => hD τ t ht hre (le_trans (le_max_left Yc 2) hYτ) ht1
  -- The two slashed-kernel cusp bounds, with the common threshold `Y`.
  obtain ⟨Cp, Ap, hCp, hAp, hKp⟩ := KPlus_tail_lines_twentyfour ℓ c Y hc hY2 hD'
  obtain ⟨Cm, Am, hCm, hAm, hKm⟩ := KMinus_tail_lines_twentyfour ℓ c Y hc hY2 hD'
  -- The common exponent and constant.
  set A : ℝ := max Ap Am with hAdef
  have hA0 : 0 ≤ A := le_trans hAp (le_max_left Ap Am)
  have hApA : Ap ≤ A := le_max_left Ap Am
  have hAmA : Am ≤ A := le_max_right Ap Am
  refine ⟨2 * (Cp + Cm), A, Y, by positivity, hA0, hY1, ?_⟩
  intro τ t ht hre hYτ ht1
  set E : ℝ := Real.exp (-(2 * Real.pi * τ.im)) *
      (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hsτ1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hsτ0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have hXA0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg hsτ0 A
  -- Each slashed kernel is bounded by the common majorant with constant `Cp + Cm`.
  have hbp : t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
      ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * E := by
    have hp := hKp τ t ht hre hYτ ht1
    calc t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
        ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * E := by rw [hEdef]; exact hp
      _ ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ A * E :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hsτ1 hApA) hCp) hE0
      _ ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hXA0) hE0
  have hbm : t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
      ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * E := by
    have hm := hKm τ t ht hre hYτ ht1
    calc t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
        ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am * E := by rw [hEdef]; exact hm
      _ ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ A * E :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hsτ1 hAmA) hCm) hE0
      _ ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hXA0) hE0
  have hsum : t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
        + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)
      ≤ 2 * (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * E := by
    rw [mul_add]
    calc t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
          + t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
        ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * E
          + (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * E := add_le_add hbp hbm
      _ = 2 * (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * E := by ring
  have haxis := Phi_axis_norm_twentyfour ℓ τ ht
  rw [hEdef] at hsum
  exact ⟨le_trans haxis.1 hsum, le_trans haxis.2 hsum⟩

end Work.CKFinal.LineDecay

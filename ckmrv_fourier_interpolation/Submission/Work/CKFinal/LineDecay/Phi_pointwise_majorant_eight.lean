import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.Phi_axis_norm_eight
import Submission.Work.CKFinal.LineDecay.DenomLower_lines
import Submission.Work.CKFinal.LineDecay.KPlus_tail_lines
import Submission.Work.CKFinal.LineDecay.KMinus_tail_lines

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-- **Numerical assembly of the pointwise majorant.**

Given the two slashed-kernel bounds at a fixed point `z = S • (i t)` (`t > 0`),
`t² ‖K₊(τ, z)‖ ≤ Cp (1+‖τ‖)^{Ap} E` and
`t² ‖K₋(τ, z)‖ ≤ Cm (1+‖τ‖)^{Am} (1+t)^{Am} E` for a nonnegative factor `E`, both
`t² ‖K₊‖ + t² ‖K₋‖` and (hence) `‖Φ‖ ≤ t²(‖K₊‖ + ‖K₋‖)` are bounded by the single
majorant `(Cp + Cm) (1+‖τ‖)^{max Ap Am} ((1+t)^{max Ap Am} E)`.

The exponent `A = max Ap Am` is large enough for both bounds, and the extra factor
`(1+t)^A ≥ 1` of the `K₋` bound is harmless. -/
private lemma combine_common {ℓ : Work.Kernels.LogLambdaData} {τ : UpperHalfPlane} {t E : ℝ}
    (ht : 0 < t) {Cp Cm Ap Am : ℝ} (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hAp : 0 ≤ Ap)
    (hE0 : 0 ≤ E)
    (hp : t ^ 2 * ‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
        ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * E)
    (hm : t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
        ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am * E) :
    t ^ 2 * (‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
        + ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)
      ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E) := by
  have hA0 : (0 : ℝ) ≤ max Ap Am := le_trans hAp (le_max_left Ap Am)
  have hs1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
    have h := norm_nonneg ((τ : ℂ)); linarith
  have hs0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hXnn : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) := Real.rpow_nonneg hs0 _
  have hone : (1 : ℝ) ≤ (1 + t) ^ (max Ap Am) := Real.one_le_rpow ht1 hA0
  have hpA : (1 + ‖(τ : ℂ)‖) ^ Ap ≤ (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left Ap Am)
  have hmA : (1 + ‖(τ : ℂ)‖) ^ Am ≤ (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right Ap Am)
  have hmT : (1 + t) ^ Am ≤ (1 + t) ^ (max Ap Am) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right Ap Am)
  have hp' : t ^ 2 * ‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
      ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E) := by
    have h1 : Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * E
        ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpA hCp) hE0
    have h2 : E ≤ (1 + t) ^ (max Ap Am) * E := le_mul_of_one_le_left hE0 hone
    have h3 : Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * E
        ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E) := by
      have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hCp hXnn)
      calc Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * E
          = (Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am)) * E := by ring
        _ ≤ (Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am)) * ((1 + t) ^ (max Ap Am) * E) := h4
        _ = Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E) := by ring
    exact le_trans hp (le_trans h1 h3)
  have hm' : t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
      ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E) := by
    have h2 : (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am
        ≤ (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) :=
      mul_le_mul hmA hmT (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) Am) hXnn
    have h3 : Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am
        ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) := by
      calc Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am
          = Cm * ((1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am) := by ring
        _ ≤ Cm * ((1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am)) :=
            mul_le_mul_of_nonneg_left h2 hCm
        _ = Cm * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) := by ring
    have h4 : Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am * E
        ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) * E :=
      mul_le_mul_of_nonneg_right h3 hE0
    have h5 : Cm * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) * E
        = Cm * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E) := by ring
    exact le_trans hm (le_trans h4 (le_of_eq h5))
  calc t ^ 2 * (‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
          + ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)
      = t ^ 2 * ‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
        + t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖ := by
        ring
    _ ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E)
        + Cm * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E) :=
        add_le_add hp' hm'
    _ = (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * ((1 + t) ^ (max Ap Am) * E) := by ring

/-- **Pointwise majorant for the second difference `Φ` of both dimension-8 kernels on the two
lines `Re τ = ±1/2`.**

For `τ` with `Re τ = ±1/2` and `Im τ ≥ Y₀` (large) and for `t ≥ 1`,
`‖Φ(K^{(8)})(τ,i t)‖` and `‖Φ(K̂^{(8)})(τ,i t)‖` are both bounded by
`C (1+‖τ‖)^A · (1+t)^A · e^{-πt}/(1 + e^{2π(Im τ - t)})`.

This is the `t`-pointwise strengthening of `Work.CKFinal.LineDecay.Phi_tail_bound_eight` (which
integrates over `t ≥ 1`), for *both* kernels, and it is exactly the pointwise input needed to
bound the tail piece `P₃` of the contour shift. The proof combines the axis reduction
`Φ = -(i t)^2 (K₊ ∓ K₋)` (`Work.CKFinal.Phi_axis_eq`, `Work.CKFinal.PhiHat_axis_eq`, together
with `‖(i t)^2‖ = t^2`) with the two slashed-kernel bounds `KPlus_tail_lines` and
`KMinus_tail_lines` (whose divisor input is `DenomLower_lines`); the exponent `A := max A₊ A₋`
absorbs the `(1+t)^{A₋}` factor of the `K₋` bound since `(1+t)^A ≥ 1` for `A ≥ 0`, `t ≥ 1`. -/
theorem Phi_pointwise_majorant_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im → 1 ≤ t →
        (‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 8) τ t‖
            ≤ C * (1 + ‖(τ : ℂ)‖) ^ A *
              ((1 + t) ^ A * (Real.exp (-(Real.pi * t))
                / (1 + Real.exp (2 * Real.pi * (τ.im - t))))))
          ∧ (‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 8) τ t‖
            ≤ C * (1 + ‖(τ : ℂ)‖) ^ A *
              ((1 + t) ^ A * (Real.exp (-(Real.pi * t))
                / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))) := by
  -- The divisor lower bound on the two lines and the two slashed-kernel bounds.
  obtain ⟨c, Yc, hc, hYc, hD⟩ := DenomLower_lines
  obtain ⟨Cp, Ap, hCp, hAp, hKp⟩ := KPlus_tail_lines c Yc hc hYc hD
  obtain ⟨Cm, Am, hCm, hAm, hKm⟩ := KMinus_tail_lines ℓ c Yc hc hYc hD
  refine ⟨Cp + Cm, max Ap Am, Yc, by linarith, le_trans hAp (le_max_left Ap Am), hYc, ?_⟩
  intro τ t hre hY h1t
  have ht : (0 : ℝ) < t := by linarith
  set E : ℝ := Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))) with hE
  have hE0 : (0 : ℝ) ≤ E := by rw [hE]; positivity
  have hp : t ^ 2 * ‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
      ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * E := by
    rw [hE]; exact hKp τ t ht hre hY h1t
  have hm : t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
      ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am * E := by
    rw [hE]; exact hKm τ t ht hre hY h1t
  have hsum := combine_common ht hCp hCm hAp hE0 hp hm
  obtain ⟨h1, h2⟩ := Phi_axis_norm_eight ℓ τ ht
  exact ⟨le_trans h1 hsum, le_trans h2 hsum⟩

end

end Work.CKFinal.LineDecay

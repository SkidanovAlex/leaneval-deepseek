import Mathlib

/-!
# Interpolation of `Lᵖ` seminorms and of bilinear forms

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), repeatedly use the *interpolation* of `ℓᵖ` estimates: an estimate
proved at one pair of exponents is upgraded to the exponents needed in the application, and the
dependent constants are combined log-convexly.  Section 5 uses it to pass from the single-scale
minor arc estimate (which is proved for `ℓ²(ℤ) × ℓ²(ℤ) → ℓ¹(ℤ)`) to the exponents of Theorem
1.17; §6 and §10 use the same principle for the `ℓᵖ`-improving and arithmetic bilinear estimates.

Mathlib contains Hadamard's three-lines theorem (`Mathlib.Analysis.Complex.Hadamard`) but no
Riesz--Thorin interpolation.  This file builds the chapter:

* `lintegral_enorm_rpow_interp` / `eLpNorm_interp`: the log-convexity (Lyapunov) interpolation of
  the `Lᵖ` seminorm itself, an immediate consequence of Hölder's inequality;
* `interp_strip_bound` and `riesz_thorin_bilinear_form`: interpolation for bilinear forms, proved
  by Hadamard's three-lines theorem applied to the analytic family
  `z ↦ Λ(|f|^{a(z)} u, |g|^{b(z)} v)` of a *finite* (simple) pair of test functions.

The statements are given for arbitrary measure spaces; the functions are `ℂ`-valued and the
seminorms are the extended ones (`MeasureTheory.eLpNorm`), so that no finiteness of the measure
and no integrability hypothesis beyond measurability is needed.
-/

set_option maxHeartbeats 1600000

namespace Interp

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ## Log-convexity of the `Lᵖ` seminorm -/

/-- **Hölder interpolation of the `ℒᵖ` integral.**  For `0 < p` and real exponents `p₀, p₁` and
`θ ∈ [0,1]` with `1/p = (1-θ)/p₀ + θ/p₁`,
`∫ ‖f‖^p ≤ (∫ ‖f‖^{p₀})^{(1-θ)p/p₀} (∫ ‖f‖^{p₁})^{θp/p₁}`. -/
theorem lintegral_enorm_rpow_interp {f : α → ℂ} {p₀ p₁ p θ : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp : 0 < p)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hrel : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hf : AEMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤
      (∫⁻ x, ‖f x‖ₑ ^ p₀ ∂μ) ^ ((1 - θ) * p / p₀) *
        (∫⁻ x, ‖f x‖ₑ ^ p₁ ∂μ) ^ (θ * p / p₁) := by
  have hu_pos : 0 < (1 - θ) * p / p₀ := by positivity
  have hv_pos : 0 < θ * p / p₁ := by positivity
  have hsum : p₀ * ((1 - θ) * p / p₀) + p₁ * (θ * p / p₁) = p := by
    have h : p * ((1 - θ) / p₀ + θ / p₁) = 1 := by rw [← hrel]; field_simp
    field_simp
    nlinarith [h]
  have huv : (1 - θ) * p / p₀ + θ * p / p₁ = 1 := by
    have h : p * ((1 - θ) / p₀ + θ / p₁) = 1 := by rw [← hrel]; field_simp
    have h2 : (1 - θ) * p / p₀ + θ * p / p₁ = p * ((1 - θ) / p₀ + θ / p₁) := by ring
    rw [h2, h]
  have hconj : (1 / ((1 - θ) * p / p₀)).HolderConjugate (1 / (θ * p / p₁)) :=
    ⟨by rw [one_div, one_div, inv_inv, inv_inv, inv_one]; exact huv, by positivity, by positivity⟩
  have hf₁ : AEMeasurable (fun x => ‖f x‖ₑ ^ p₀) μ := hf.enorm.pow_const p₀
  have hf₂ : AEMeasurable (fun x => ‖f x‖ₑ ^ p₁) μ := hf.enorm.pow_const p₁
  have hg₁ : AEMeasurable (fun x => (‖f x‖ₑ ^ p₀) ^ ((1 - θ) * p / p₀)) μ :=
    hf₁.pow_const _
  have hg₂ : AEMeasurable (fun x => (‖f x‖ₑ ^ p₁) ^ (θ * p / p₁)) μ := hf₂.pow_const _
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hg₁ hg₂
  have hmul : (fun x => (‖f x‖ₑ ^ p₀) ^ ((1 - θ) * p / p₀)
        * (‖f x‖ₑ ^ p₁) ^ (θ * p / p₁)) = fun x => ‖f x‖ₑ ^ p := by
    funext x
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_add_pos (by rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_top)
        _ _ (by rw [hsum]; exact hp)]
    rw [hsum]
  have hg₁' : (fun x => ((‖f x‖ₑ ^ p₀) ^ ((1 - θ) * p / p₀))
        ^ (1 / ((1 - θ) * p / p₀))) = fun x => ‖f x‖ₑ ^ p₀ := by
    funext x
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hu_pos), ENNReal.rpow_one]
  have hg₂' : (fun x => ((‖f x‖ₑ ^ p₁) ^ (θ * p / p₁))
        ^ (1 / (θ * p / p₁))) = fun x => ‖f x‖ₑ ^ p₁ := by
    funext x
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hv_pos), ENNReal.rpow_one]
  simp only [Pi.mul_apply] at hholder
  rw [show (1 : ℝ) / (1 / ((1 - θ) * p / p₀)) = (1 - θ) * p / p₀ from by
    rw [one_div, one_div, inv_inv]] at hholder
  rw [show (1 : ℝ) / (1 / (θ * p / p₁)) = θ * p / p₁ from by
    rw [one_div, one_div, inv_inv]] at hholder
  rw [hmul, hg₁', hg₂'] at hholder
  exact hholder


/-- **Log-convexity of the `Lᵖ` seminorm** (Lyapunov interpolation): for `θ ∈ (0,1)` and
`1/p = (1-θ)/p₀ + θ/p₁` one has `‖f‖_p ≤ ‖f‖_{p₀}^{1-θ} ‖f‖_{p₁}^{θ}`. -/
theorem eLpNorm_interp {f : α → ℂ} {p₀ p₁ p θ : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp : 0 < p)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hrel : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hf : AEMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal p₀) μ ^ (1 - θ) * eLpNorm f (ENNReal.ofReal p₁) μ ^ θ := by
  have h := lintegral_enorm_rpow_interp (μ := μ) (f := f) hp₀ hp₁ hp hθ₀ hθ₁ hrel hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf.aestronglyMeasurable) (p := ENNReal.ofReal p)
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf.aestronglyMeasurable) (p := ENNReal.ofReal p₀)
        (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf.aestronglyMeasurable) (p := ENNReal.ofReal p₁)
        (ENNReal.ofReal_ne_zero_iff.mpr hp₁) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hp₀.le, ENNReal.toReal_ofReal hp₁.le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  refine (ENNReal.rpow_le_rpow h (by positivity : (0:ℝ) ≤ 1 / p)).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / p)]
  congr 1
  · rw [← ENNReal.rpow_mul]; congr 1; field_simp
  · rw [← ENNReal.rpow_mul]; congr 1; field_simp

end Interp

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open MeasureTheory
open scoped Real
open scoped ENNReal

namespace Commons.Measure.Integral

/-- Real factorization underlying the Hölder step: for `0 < p ≤ p₀` and nonnegative `nx`, `wx`,
`nx^p * wx = (nx^p₀ * wx)^(p/p₀) * wx^(1 - p/p₀)`. -/
private lemma real_factor {p p₀ nx wx : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) (hpp₀ : p ≤ p₀)
    (hnx : 0 ≤ nx) (hwx : 0 ≤ wx) :
    nx ^ p * wx = (nx ^ p₀ * wx) ^ (p / p₀) * wx ^ (1 - p / p₀) := by
  have hnxp₀ : 0 ≤ nx ^ p₀ := Real.rpow_nonneg hnx p₀
  have ha0 : 0 ≤ p / p₀ := div_nonneg (le_of_lt hp) (le_of_lt hp₀)
  have hb0 : 0 ≤ 1 - p / p₀ := by
    rw [sub_nonneg]
    exact (div_le_one hp₀).2 hpp₀
  calc
    nx ^ p * wx = nx ^ p * wx ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = nx ^ (p₀ * (p / p₀)) * wx ^ (1 : ℝ) := by
      congr 1
      field_simp [ne_of_gt hp₀]
    _ = nx ^ (p₀ * (p / p₀)) * wx ^ (p / p₀ + (1 - p / p₀)) := by
      congr 1
      ring_nf
    _ = nx ^ (p₀ * (p / p₀)) * (wx ^ (p / p₀) * wx ^ (1 - p / p₀)) := by
      rw [Real.rpow_add_of_nonneg hwx ha0 hb0]
    _ = (nx ^ p₀ * wx) ^ (p / p₀) * wx ^ (1 - p / p₀) := by
      rw [Real.mul_rpow hnxp₀ hwx]
      rw [Real.rpow_mul hnx]
      ring_nf

/-- The same factorization lifted to `ℝ≥0∞` through `ENNReal.ofReal`. -/
private lemma ennreal_factor {p p₀ nx wx : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) (hpp₀ : p ≤ p₀)
    (hnx : 0 ≤ nx) (hwx : 0 ≤ wx) :
    ENNReal.ofReal (nx ^ p * wx) =
      (ENNReal.ofReal (nx ^ p₀ * wx)) ^ (p / p₀) *
        (ENNReal.ofReal wx) ^ (1 - p / p₀) := by
  have hψx : 0 ≤ nx ^ p₀ * wx := mul_nonneg (Real.rpow_nonneg hnx p₀) hwx
  have ha0 : 0 ≤ p / p₀ := div_nonneg (le_of_lt hp) (le_of_lt hp₀)
  have hb0 : 0 ≤ 1 - p / p₀ := by
    rw [sub_nonneg]
    exact (div_le_one hp₀).2 hpp₀
  have hψxa : 0 ≤ (nx ^ p₀ * wx) ^ (p / p₀) := Real.rpow_nonneg hψx (p / p₀)
  rw [real_factor hp hp₀ hpp₀ hnx hwx]
  rw [ENNReal.ofReal_mul hψxa]
  rw [← ENNReal.ofReal_rpow_of_nonneg hψx ha0]
  rw [← ENNReal.ofReal_rpow_of_nonneg hwx hb0]

/-- Hölder's inequality for weighted power integrals with real exponents: if
`0 < p ≤ p₀` and `w ≥ 0` pointwise, then

    (∫ ‖f‖^p · w)^(1/p) ≤ (∫ ‖f‖^p₀ · w)^(1/p₀) · (∫ w)^(1/p − 1/p₀) .

This is the estimate behind the `2 ≤ p ≤ p₀` half of the discrete restriction
bounds. Proof route: raise both sides as needed and apply Hölder with
conjugate exponents `p₀/p` and `p₀/(p₀−p)` to the identity
`‖f‖^p·w = (‖f‖^{p₀}·w)^(p/p₀) · w^(1−p/p₀)` (equivalently
`ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr` / `ENNReal.lintegral_mul_le_Lp_mul_Lq`),
then transfer the lintegral inequalities to the real Bochner integrals via the
standard nonneg conversions (`integral_eq_lintegral_of_nonneg_ae`,
`lintegral_ofReal`, `ENNReal.toReal_rpow`). -/
theorem holder_pow_le_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) {p p₀ : ℝ}
    (hp : 0 < p) (hp₀ : 0 < p₀) (hpp₀ : p ≤ p₀) (f : α → ℂ) (w : α → ℝ)
    (hw_nonneg : ∀ x, 0 ≤ w x)
    (hf : AEMeasurable f μ) (hw_meas : AEMeasurable w μ)
    (hfp : Integrable (fun x => ‖f x‖ ^ p * w x) μ)
    (hfp₀ : Integrable (fun x => ‖f x‖ ^ p₀ * w x) μ)
    (hwint : Integrable w μ) :
    (∫ x, ‖f x‖ ^ p * w x ∂μ) ^ (1 / p) ≤
      (∫ x, ‖f x‖ ^ p₀ * w x ∂μ) ^ (1 / p₀) * (∫ x, w x ∂μ) ^ (1 / p - 1 / p₀) := by
  classical
  -- pointwise nonnegativity of the three integrands
  have hφx : ∀ x, 0 ≤ ‖f x‖ ^ p * w x := fun x =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) p) (hw_nonneg x)
  have hψx : ∀ x, 0 ≤ ‖f x‖ ^ p₀ * w x := fun x =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) p₀) (hw_nonneg x)
  have ha0 : 0 ≤ p / p₀ := div_nonneg (le_of_lt hp) (le_of_lt hp₀)
  have hb0 : 0 ≤ 1 - p / p₀ := by
    rw [sub_nonneg]
    exact (div_le_one hp₀).2 hpp₀
  have hab : p / p₀ + (1 - p / p₀) = 1 := by ring_nf
  -- main estimate in the `ℝ≥0∞` (lintegral) world
  have hmain_enn :
      (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p * w x) ∂μ) ≤
        (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p₀ * w x) ∂μ) ^ (p / p₀) *
          (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ^ (1 - p / p₀) := by
    let U : α → ℝ≥0∞ := fun x => ENNReal.ofReal (‖f x‖ ^ p₀ * w x)
    let V : α → ℝ≥0∞ := fun x => ENNReal.ofReal (w x)
    have hU : AEMeasurable U μ := by
      dsimp [U]
      fun_prop
    have hV : AEMeasurable V μ := by
      dsimp [V]
      fun_prop
    calc
      (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p * w x) ∂μ)
          = ∫⁻ x, U x ^ (p / p₀) * V x ^ (1 - p / p₀) ∂μ := by
            apply lintegral_congr
            intro x
            simpa [U, V] using ennreal_factor (nx := ‖f x‖) (wx := w x) hp hp₀ hpp₀
              (norm_nonneg (f x)) (hw_nonneg x)
      _ ≤ (∫⁻ x, U x ∂μ) ^ (p / p₀) * (∫⁻ x, V x ∂μ) ^ (1 - p / p₀) := by
            exact ENNReal.lintegral_mul_norm_pow_le hU hV ha0 hb0 hab
  -- lintegral identities for the three Bochner integrals
  have hA_lin : ENNReal.ofReal (∫ x, ‖f x‖ ^ p * w x ∂μ) =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p * w x) ∂μ :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfp (ae_of_all μ hφx)
  have hB_lin : ENNReal.ofReal (∫ x, ‖f x‖ ^ p₀ * w x ∂μ) =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p₀ * w x) ∂μ :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfp₀ (ae_of_all μ hψx)
  have hC_lin : ENNReal.ofReal (∫ x, w x ∂μ) =
      ∫⁻ x, ENNReal.ofReal (w x) ∂μ :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hwint (ae_of_all μ hw_nonneg)
  -- nonnegativity of the integrals themselves
  have hA0 : 0 ≤ ∫ x, ‖f x‖ ^ p * w x ∂μ := integral_nonneg hφx
  have hB0 : 0 ≤ ∫ x, ‖f x‖ ^ p₀ * w x ∂μ := integral_nonneg hψx
  have hC0 : 0 ≤ ∫ x, w x ∂μ := integral_nonneg hw_nonneg
  have hBap : 0 ≤ (∫ x, ‖f x‖ ^ p₀ * w x ∂μ) ^ (p / p₀) :=
    Real.rpow_nonneg hB0 (p / p₀)
  have hCbp : 0 ≤ (∫ x, w x ∂μ) ^ (1 - p / p₀) := Real.rpow_nonneg hC0 (1 - p / p₀)
  have hRhs : 0 ≤ (∫ x, ‖f x‖ ^ p₀ * w x ∂μ) ^ (p / p₀) * (∫ x, w x ∂μ) ^ (1 - p / p₀) :=
    mul_nonneg hBap hCbp
  -- real main estimate
  have h_main :
      (∫ x, ‖f x‖ ^ p * w x ∂μ) ≤
        (∫ x, ‖f x‖ ^ p₀ * w x ∂μ) ^ (p / p₀) *
          (∫ x, w x ∂μ) ^ (1 - p / p₀) := by
    rw [← ENNReal.ofReal_le_ofReal_iff hRhs]
    calc
      ENNReal.ofReal (∫ x, ‖f x‖ ^ p * w x ∂μ)
          ≤ (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p₀ * w x) ∂μ) ^ (p / p₀) *
              (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ^ (1 - p / p₀) := by
            simpa [hA_lin] using hmain_enn
      _ = ENNReal.ofReal ((∫ x, ‖f x‖ ^ p₀ * w x ∂μ) ^ (p / p₀) *
              (∫ x, w x ∂μ) ^ (1 - p / p₀)) := by
            rw [← hB_lin, ← hC_lin]
            rw [ENNReal.ofReal_rpow_of_nonneg hB0 ha0]
            rw [ENNReal.ofReal_rpow_of_nonneg hC0 hb0]
            rw [ENNReal.ofReal_mul hBap]
  -- raise both sides of the real estimate to the power `1 / p`
  have h_inv : 0 < 1 / p := one_div_pos.mpr hp
  calc
    (∫ x, ‖f x‖ ^ p * w x ∂μ) ^ (1 / p)
        ≤ ((∫ x, ‖f x‖ ^ p₀ * w x ∂μ) ^ (p / p₀) *
            (∫ x, w x ∂μ) ^ (1 - p / p₀)) ^ (1 / p) :=
          Real.rpow_le_rpow hA0 h_main (le_of_lt h_inv)
    _ = (∫ x, ‖f x‖ ^ p₀ * w x ∂μ) ^ (1 / p₀) *
          (∫ x, w x ∂μ) ^ (1 / p - 1 / p₀) := by
          rw [Real.mul_rpow hBap hCbp]
          rw [← Real.rpow_mul hB0, ← Real.rpow_mul hC0]
          congr 1
          · field_simp [ne_of_gt hp, ne_of_gt hp₀]
          · field_simp [ne_of_gt hp, ne_of_gt hp₀]

end Commons.Measure.Integral
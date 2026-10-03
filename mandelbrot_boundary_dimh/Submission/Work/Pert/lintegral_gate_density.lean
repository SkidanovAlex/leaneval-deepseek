import Mathlib

/-!
# `Work.Pert.lintegral_gate_density`

The one-dimensional gate density of Shishikura §4.2: the (even) function

`u ↦ if |u| ≤ δ then (16 δ²)⁻¹ else (4 π² u²)⁻¹`

has total mass at most `1/(2δ)`.  The bound is proved by comparing it with the Cauchy
density `u ↦ (1/8)(δ² + u²)⁻¹`, whose total mass is exactly `π/(8δ) < 1/(2δ)`:

* on `|u| ≤ δ` one has `(16δ²)⁻¹ ≤ (1/8)(δ²+u²)⁻¹` because `δ² + u² ≤ 2δ²`;
* on `|u| > δ` one has `(4π²u²)⁻¹ ≤ (1/8)(δ²+u²)⁻¹` because `δ² + u² < 2u²` and `π > 2`.
-/

namespace Work.Pert

/-- The total mass `π/δ` of the Cauchy density `u ↦ (δ² + u²)⁻¹` (`δ > 0`). -/
theorem integral_inv_sq_add_sq_delta {δ : ℝ} (hδ : 0 < δ) :
    ∫ u : ℝ, (δ ^ 2 + u ^ 2)⁻¹ = Real.pi / δ := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hb : δ⁻¹ ≠ 0 := inv_ne_zero hδ0
  have hfun : (fun u : ℝ => (δ ^ 2 + u ^ 2)⁻¹)
      = fun u => (δ ^ 2)⁻¹ * (1 + (δ⁻¹ * u) ^ 2)⁻¹ := by
    funext u; field_simp
  rw [hfun, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_mul_sq,
    abs_of_pos (inv_pos.mpr hδ)]
  field_simp

/-- The Cauchy density `u ↦ (δ²+u²)⁻¹` is integrable for `δ > 0`. -/
theorem integrable_inv_sq_add_sq_delta {δ : ℝ} (hδ : 0 < δ) :
    MeasureTheory.Integrable (fun u : ℝ => (δ ^ 2 + u ^ 2)⁻¹) := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hb : δ⁻¹ ≠ 0 := inv_ne_zero hδ0
  have hfun : (fun u : ℝ => (δ ^ 2 + u ^ 2)⁻¹)
      = fun u => (δ ^ 2)⁻¹ * (1 + (δ⁻¹ * u) ^ 2)⁻¹ := by
    funext u; field_simp
  rw [hfun]
  exact (integrable_inv_one_add_mul_sq hb).const_mul _

/-- Pointwise comparison of the gate density with the Cauchy density `(1/8)(δ²+u²)⁻¹`. -/
theorem gate_density_le_cauchy {δ u : ℝ} (hδ : 0 < δ) :
    (if |u| ≤ δ then (16 * δ ^ 2)⁻¹ else (4 * Real.pi ^ 2 * u ^ 2)⁻¹)
      ≤ (1 / 8) * (δ ^ 2 + u ^ 2)⁻¹ := by
  have heq : (1 / 8 : ℝ) * (δ ^ 2 + u ^ 2)⁻¹ = (8 * (δ ^ 2 + u ^ 2))⁻¹ := by
    rw [show (1 / 8 : ℝ) = 8⁻¹ by norm_num, mul_inv]
  by_cases hu : |u| ≤ δ
  · rw [ite_eq_left hu, heq, inv_le_inv₀ (by positivity) (by positivity)]
    have hu2 : u ^ 2 ≤ δ ^ 2 := by
      calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
        _ ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg u) hu 2
    nlinarith [hu2]
  · have hu0 : u ≠ 0 := by
      intro h; exact hu (by rw [h, abs_zero]; exact le_of_lt hδ)
    rw [ite_eq_right hu, heq, inv_le_inv₀ _ (by positivity)]
    · have hu2 : δ ^ 2 < u ^ 2 := by
        rw [sq_lt_sq, abs_of_pos hδ]
        exact lt_of_not_ge hu
      have hπ : (4 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have hπu : 4 * u ^ 2 < Real.pi ^ 2 * u ^ 2 :=
        mul_lt_mul_of_pos_right hπ (sq_pos_of_ne_zero hu0)
      nlinarith [hu2, hπu, sq_nonneg u]
    · have : (0 : ℝ) < u ^ 2 := sq_pos_of_ne_zero hu0
      positivity

theorem lintegral_gate_density {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ u : ℝ, ENNReal.ofReal
        (if |u| ≤ δ then (16 * δ ^ 2)⁻¹ else (4 * Real.pi ^ 2 * u ^ 2)⁻¹)
      ≤ ENNReal.ofReal (1 / (2 * δ)) := by
  have hInt1 : MeasureTheory.Integrable (fun u : ℝ => (δ ^ 2 + u ^ 2)⁻¹) :=
    integrable_inv_sq_add_sq_delta hδ
  have hval : ∫ u : ℝ, (δ ^ 2 + u ^ 2)⁻¹ = Real.pi / δ :=
    integral_inv_sq_add_sq_delta hδ
  have hInt2 : MeasureTheory.Integrable (fun u : ℝ => (1 / 8) * (δ ^ 2 + u ^ 2)⁻¹) :=
    hInt1.const_mul _
  have hnn : 0 ≤ᵐ[MeasureTheory.volume] (fun u : ℝ => (1 / 8) * (δ ^ 2 + u ^ 2)⁻¹) :=
    Filter.Eventually.of_forall fun u => by positivity
  calc ∫⁻ u : ℝ, ENNReal.ofReal
          (if |u| ≤ δ then (16 * δ ^ 2)⁻¹ else (4 * Real.pi ^ 2 * u ^ 2)⁻¹)
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal ((1 / 8) * (δ ^ 2 + u ^ 2)⁻¹) :=
        MeasureTheory.lintegral_mono fun u => ENNReal.ofReal_le_ofReal (gate_density_le_cauchy hδ)
    _ = ENNReal.ofReal (∫ u : ℝ, (1 / 8) * (δ ^ 2 + u ^ 2)⁻¹) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2 hnn).symm
    _ = ENNReal.ofReal (Real.pi / (8 * δ)) := by
        rw [MeasureTheory.integral_const_mul, hval]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (1 / (2 * δ)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : (1 : ℝ) / (2 * δ) = 4 / (8 * δ) := by field_simp; ring
        rw [h1]
        exact div_le_div_of_nonneg_right (le_of_lt Real.pi_lt_four) (by positivity)

end Work.Pert

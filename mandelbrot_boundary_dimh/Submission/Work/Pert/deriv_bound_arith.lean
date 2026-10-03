import Mathlib

/-!
# Elementary norm estimate for the perturbed-coordinate derivative (Shishikura, PERT area)

We prove the arithmetic lemma `deriv_bound_arith` used to bound the derivative of the perturbed
Fatou coordinate.  With `c = 2πi`, `w = σ/α`, the expression appearing in the goal is

  `E = -(c * α/σ) - c * α * p = -(c * w⁻¹ + c * (α*p))`,

so `‖E/D‖ = ‖c * w⁻¹ + c * (α*p)‖ / ‖D‖`.  The hypothesis `‖σ/α + c‖ ≤ 1/16` puts `w` in the
annulus `[2π - 1/16, 2π + 1/16]`, whence `‖c * w⁻¹‖ ∈ (96/97, 96/95)` (using only `3 < π`), while
`‖α*p‖ ≤ 51/655360` is tiny; hence `‖E‖ ∈ (2/3, 3/2)`.  Finally `‖D - 1‖ ≤ 1/4` gives
`‖D‖ ∈ [3/4, 5/4]`, and `(2/3)/(5/4) = 8/15 > 1/2`, `(3/2)/(3/4) = 2`.

The whole estimate is deliberately loose; nothing here needs a sharp bound on `π`.
-/

set_option linter.unusedVariables false

namespace Work.Pert

/-- `‖2πi‖ = 2π`. -/
lemma norm_two_pi_I : ‖(2 : ℂ) * Real.pi * Complex.I‖ = 2 * Real.pi := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- If `w` is within `1/16` of `-2πi` and `q` is small (`‖q‖ ≤ 1/1000`), then
`‖(2πi) w⁻¹ + q‖` lies in `(2/3, 3/2)`. -/
lemma norm_two_pi_inv_add_bound {w q : ℂ}
    (hw : ‖w + 2 * Real.pi * Complex.I‖ ≤ 1 / 16) (hq : ‖q‖ ≤ 1 / 1000) :
    2 / 3 < ‖(2 * Real.pi * Complex.I) * w⁻¹ + q‖ ∧
      ‖(2 * Real.pi * Complex.I) * w⁻¹ + q‖ < 3 / 2 := by
  have hden : 0 < 2 * Real.pi - 1 / 16 := by nlinarith [Real.pi_gt_three]
  have hw_lower : 2 * Real.pi - 1 / 16 ≤ ‖w‖ := by
    have h1 : ‖(2 : ℂ) * Real.pi * Complex.I‖ ≤ ‖w + 2 * Real.pi * Complex.I‖ + ‖w‖ := by
      calc ‖(2 : ℂ) * Real.pi * Complex.I‖ = ‖(w + 2 * Real.pi * Complex.I) - w‖ := by
            congr 1; ring
        _ ≤ ‖w + 2 * Real.pi * Complex.I‖ + ‖w‖ := norm_sub_le _ _
    rw [norm_two_pi_I] at h1
    linarith
  have hw_upper : ‖w‖ ≤ 2 * Real.pi + 1 / 16 := by
    have h1 : ‖w‖ ≤ ‖w + 2 * Real.pi * Complex.I‖ + ‖(2 : ℂ) * Real.pi * Complex.I‖ := by
      calc ‖w‖ = ‖(w + 2 * Real.pi * Complex.I) - (2 : ℂ) * Real.pi * Complex.I‖ := by
            congr 1; ring
        _ ≤ ‖w + 2 * Real.pi * Complex.I‖ + ‖(2 : ℂ) * Real.pi * Complex.I‖ := norm_sub_le _ _
    rw [norm_two_pi_I] at h1
    linarith
  have hw_inv_le : ‖w⁻¹‖ ≤ 1 / (2 * Real.pi - 1 / 16) := by
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hden hw_lower
  have hw_inv_ge : 1 / (2 * Real.pi + 1 / 16) ≤ ‖w⁻¹‖ := by
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) hw_upper
  have htwo_pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have htwo_pi_den_pos : (0 : ℝ) < 2 * Real.pi + 1 / 16 := by nlinarith [Real.pi_gt_three]
  have hcw_le : ‖(2 * Real.pi * Complex.I) * w⁻¹‖ ≤ 96 / 95 := by
    rw [norm_mul, norm_two_pi_I]
    calc (2 * Real.pi) * ‖w⁻¹‖
        ≤ (2 * Real.pi) * (1 / (2 * Real.pi - 1 / 16)) :=
          mul_le_mul_of_nonneg_left hw_inv_le (le_of_lt htwo_pi_pos)
      _ = (2 * Real.pi) / (2 * Real.pi - 1 / 16) := by rw [mul_one_div]
      _ ≤ 96 / 95 := by
          rw [div_le_iff₀ hden]
          nlinarith [Real.pi_gt_three]
  have hcw_ge : 96 / 97 ≤ ‖(2 * Real.pi * Complex.I) * w⁻¹‖ := by
    rw [norm_mul, norm_two_pi_I]
    calc (96 : ℝ) / 97
        ≤ (2 * Real.pi) / (2 * Real.pi + 1 / 16) := by
          rw [le_div_iff₀ htwo_pi_den_pos]
          nlinarith [Real.pi_gt_three]
      _ = (2 * Real.pi) * (1 / (2 * Real.pi + 1 / 16)) := by rw [mul_one_div]
      _ ≤ (2 * Real.pi) * ‖w⁻¹‖ :=
          mul_le_mul_of_nonneg_left hw_inv_ge (le_of_lt htwo_pi_pos)
  constructor
  · have h1 : ‖(2 * Real.pi * Complex.I) * w⁻¹‖ ≤
        ‖(2 * Real.pi * Complex.I) * w⁻¹ + q‖ + ‖q‖ := by
      calc ‖(2 * Real.pi * Complex.I) * w⁻¹‖
          = ‖((2 * Real.pi * Complex.I) * w⁻¹ + q) - q‖ := by congr 1; ring
        _ ≤ ‖(2 * Real.pi * Complex.I) * w⁻¹ + q‖ + ‖q‖ := norm_sub_le _ _
    have h2 : (2 : ℝ) / 3 < 96 / 97 - 1 / 1000 := by norm_num
    linarith
  · calc ‖(2 * Real.pi * Complex.I) * w⁻¹ + q‖
        ≤ ‖(2 * Real.pi * Complex.I) * w⁻¹‖ + ‖q‖ := norm_add_le _ _
      _ ≤ 96 / 95 + 1 / 1000 := add_le_add hcw_le hq
      _ < 3 / 2 := by norm_num

theorem deriv_bound_arith {σ α p D : ℂ} {η : ℝ} (hη : 0 < η)
    (hA : ‖σ / α + 2 * Real.pi * Complex.I‖ ≤ 1 / 16)
    (hαη : ‖α‖ * η ≤ 1 / 16384)
    (hp : ‖p‖ ≤ 51 * η / 40) (hD : ‖D - 1‖ ≤ 1 / 4) :
    1 / 2 < ‖(-(2 * Real.pi * Complex.I * α / σ) - 2 * Real.pi * Complex.I * α * p) / D‖ ∧
      ‖(-(2 * Real.pi * Complex.I * α / σ) - 2 * Real.pi * Complex.I * α * p) / D‖ < 2 := by
  -- `‖α * p‖ ≤ 51/655360`, hence `‖(2πi) * (α * p)‖ ≤ 1/1000`.
  have hαp : ‖α * p‖ ≤ 51 / 655360 := by
    rw [norm_mul]
    calc ‖α‖ * ‖p‖ ≤ ‖α‖ * (51 * η / 40) := mul_le_mul_of_nonneg_left hp (norm_nonneg α)
      _ = (51 / 40) * (‖α‖ * η) := by ring
      _ ≤ (51 / 40) * (1 / 16384) := mul_le_mul_of_nonneg_left hαη (by norm_num)
      _ = 51 / 655360 := by norm_num
  have hq : ‖(2 * Real.pi * Complex.I) * (α * p)‖ ≤ 1 / 1000 := by
    rw [norm_mul, norm_two_pi_I]
    calc (2 * Real.pi) * ‖α * p‖ ≤ (2 * Real.pi) * (51 / 655360) :=
          mul_le_mul_of_nonneg_left hαp (by nlinarith [Real.pi_pos])
      _ ≤ 1 / 1000 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hAux := norm_two_pi_inv_add_bound (w := σ / α)
    (q := (2 * Real.pi * Complex.I) * (α * p)) hA hq
  -- Rewrite the goal expression as `-(c * (σ/α)⁻¹ + c * (α*p))`.
  set E : ℂ := -(2 * Real.pi * Complex.I * α / σ) - 2 * Real.pi * Complex.I * α * p with hEdef
  have hEeq : E
      = -((2 * Real.pi * Complex.I) * (σ / α)⁻¹ + (2 * Real.pi * Complex.I) * (α * p)) := by
    rw [hEdef, mul_div_assoc, inv_div]
    ring
  have hE : 2 / 3 < ‖E‖ ∧ ‖E‖ < 3 / 2 := by
    rw [hEeq, norm_neg]
    exact hAux
  -- `‖D‖ ∈ [3/4, 5/4]`.
  have hD_upper : ‖D‖ ≤ 5 / 4 := by
    calc ‖D‖ = ‖(D - 1) + 1‖ := by congr 1; ring
      _ ≤ ‖D - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 := by rw [norm_one]; linarith
      _ = 5 / 4 := by norm_num
  have hD_lower : 3 / 4 ≤ ‖D‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖1 - D‖ + ‖D‖ := by
      calc ‖(1 : ℂ)‖ = ‖(1 - D) + D‖ := by congr 1; ring
        _ ≤ ‖1 - D‖ + ‖D‖ := norm_add_le _ _
    rw [norm_one, norm_sub_rev] at h1
    linarith
  have hD_pos : 0 < ‖D‖ := by linarith
  obtain ⟨hE_lo, hE_hi⟩ := hE
  rw [norm_div]
  constructor
  · rw [lt_div_iff₀ hD_pos]
    nlinarith [hE_lo, hD_upper]
  · rw [div_lt_iff₀ hD_pos]
    nlinarith [hE_hi, hD_lower]

end Work.Pert

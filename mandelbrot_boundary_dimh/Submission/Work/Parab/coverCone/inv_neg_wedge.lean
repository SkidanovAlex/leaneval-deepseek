import Mathlib

namespace Work.Parab.coverCone

/-- Numerical bound used by `inv_neg_wedge`: `cos (7π/12) = (√2 - √6)/4 ≥ -1/3`. -/
theorem cos_seven_pi_div_twelve_ge_neg_third : -(1 / 3 : ℝ) ≤ Real.cos (7 * Real.pi / 12) := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h : 7 * Real.pi / 12 = Real.pi / 3 + Real.pi / 4 := by ring
  rw [h, Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  nlinarith [hsq2, hsq3, h2, h3, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
    Real.sqrt_nonneg 6, Real.sqrt_mul h2 3]

/-- `-1/z` is `-conj z / ‖z‖²`, so its real part is `-z.re / ‖z‖²`. -/
theorem neg_inv_re_eq (z : ℂ) : (-1 / z).re = -z.re / Complex.normSq z := by
  rw [show (-1 : ℂ) / z = -(z⁻¹) by rw [div_eq_mul_inv]; ring, Complex.neg_re, Complex.inv_re,
    neg_div]

/-- `-1/z` is `-conj z / ‖z‖²`, so its imaginary part is `z.im / ‖z‖²`. -/
theorem neg_inv_im_eq (z : ℂ) : (-1 / z).im = z.im / Complex.normSq z := by
  rw [show (-1 : ℂ) / z = -(z⁻¹) by rw [div_eq_mul_inv]; ring, Complex.neg_im, Complex.inv_im]
  ring

theorem inv_neg_wedge {z : ℂ} {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hz : z ≠ 0) (harg : |z.arg| ≤ 7 * Real.pi / 12)
    (h1 : ‖z‖ ≤ 1 / (3 * M₀)) (h3 : ‖z‖ ≤ 3 / (4 * M₁))
    (hre : -M₀ ≤ (-1 / z).re) :
    M₁ < |(-1 / z).im| ∧ (-1 / z).re < 3 * |(-1 / z).im| := by
  set r := ‖z‖ with hr
  set θ := z.arg with hθ
  have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hz
  -- `-1/z = -cosθ/r + i sinθ/r`
  have hre_form : (-1 / z).re = -Real.cos θ / r := by
    rw [neg_inv_re_eq, hr, hθ, Complex.normSq_eq_norm_sq, Complex.cos_arg hz]
    field_simp
  have him_form : (-1 / z).im = Real.sin θ / r := by
    rw [neg_inv_im_eq, hr, hθ, Complex.normSq_eq_norm_sq, Complex.sin_arg z]
    field_simp
  -- the real part is bounded above by `1/3`: from `hre` and `h1`
  have hc_le : Real.cos θ ≤ 1 / 3 := by
    have hM0r : M₀ * r ≤ 1 / 3 := by
      calc M₀ * r ≤ M₀ * (1 / (3 * M₀)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hM₀)
        _ = 1 / 3 := by field_simp
    have hcr : Real.cos θ / r ≤ M₀ := by
      rw [hre_form] at hre; rw [neg_div] at hre; linarith
    calc Real.cos θ = Real.cos θ / r * r := by rw [div_mul_cancel₀ _ (ne_of_gt hrpos)]
      _ ≤ M₀ * r := mul_le_mul_of_nonneg_right hcr (le_of_lt hrpos)
      _ ≤ 1 / 3 := hM0r
  -- the real part is bounded below by `-1/3`: from `|arg z| ≤ 7π/12` and monotonicity of `cos`
  have hc_ge : -(1 / 3) ≤ Real.cos θ := by
    have h7pi : 7 * Real.pi / 12 ≤ Real.pi := by have := Real.pi_pos; nlinarith
    have hle : Real.cos (7 * Real.pi / 12) ≤ Real.cos |θ| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) h7pi harg
    rw [Real.cos_abs] at hle
    linarith [cos_seven_pi_div_twelve_ge_neg_third]
  -- hence `|cos θ| ≤ 1/3` and `|sin θ| ≥ 2√2/3`
  have hc2 : Real.cos θ ^ 2 ≤ 1 / 9 := by nlinarith [hc_le, hc_ge]
  have hs2 : 8 / 9 ≤ Real.sin θ ^ 2 := by rw [Real.sin_sq]; linarith
  have hs_ge : 2 * Real.sqrt 2 / 3 ≤ |Real.sin θ| := by
    have hsq : (2 * Real.sqrt 2 / 3) ^ 2 ≤ Real.sin θ ^ 2 := by
      have h9 : (2 * Real.sqrt 2 / 3) ^ 2 = 8 / 9 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]; norm_num
      rw [h9]; exact hs2
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 2 / 3)] at this
  constructor
  · -- first goal: `M₁ < |(-1/z).im| = |sinθ|/r`
    have hM1r : M₁ * r ≤ 3 / 4 := by
      calc M₁ * r ≤ M₁ * (3 / (4 * M₁)) := mul_le_mul_of_nonneg_left h3 (le_of_lt hM₁)
        _ = 3 / 4 := by field_simp
    have h34 : (3 : ℝ) / 4 < 2 * Real.sqrt 2 / 3 := by
      have h2n := Real.sqrt_nonneg 2
      have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    have hlt : M₁ * r < |Real.sin θ| := lt_of_le_of_lt hM1r (lt_of_lt_of_le h34 hs_ge)
    rw [him_form, abs_div, abs_of_pos hrpos]
    exact (lt_div_iff₀ hrpos).mpr hlt
  · -- second goal: `(-1/z).re = -cosθ/r < 3|sinθ|/r = 3|(-1/z).im|`
    have hnegc : -Real.cos θ ≤ 1 / 3 := by linarith
    have h3s : 2 * Real.sqrt 2 ≤ 3 * |Real.sin θ| := by linarith
    have h13 : (1 / 3 : ℝ) < 2 * Real.sqrt 2 := by
      have h2n := Real.sqrt_nonneg 2
      have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    have hlt2 : -Real.cos θ < 3 * |Real.sin θ| :=
      lt_of_lt_of_le (lt_of_le_of_lt hnegc h13) h3s
    rw [hre_form, him_form, abs_div, abs_of_pos hrpos]
    have hd := div_lt_div_of_pos_right hlt2 hrpos
    rw [mul_div_assoc] at hd
    exact hd

end Work.Parab.coverCone

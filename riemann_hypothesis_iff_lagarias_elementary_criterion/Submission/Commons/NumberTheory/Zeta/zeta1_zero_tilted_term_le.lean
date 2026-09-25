import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg

namespace Commons.NumberTheory.Zeta

/-- Every zero of `riemannZeta₁` has real part `< 1`: it is not `s = 1`, hence a zero of
`riemannZeta`, and `ζ` does not vanish on the closed half plane `re s ≥ 1`. -/
lemma zeta1_zero_re_lt_one {ρ : ℂ} (hρ : riemannZeta₁ ρ = 0) : ρ.re < 1 := by
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, riemannZeta₁_one] at hρ
    exact one_ne_zero hρ
  have hζ : riemannZeta ρ = 0 := by rw [riemannZeta_eq_inv_sub_mul hρ1, hρ, mul_zero]
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ

/-- Norm of the tilted zero summand at `ρ`, as a real expression. -/
lemma norm_zeta1_tilt (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖
      = (zeta1Order ρ : ℝ) * x ^ (ρ.re + 1) / (‖ρ‖ * ‖ρ + 1‖) := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re]

/-- For `‖ρ‖ ≥ 2` and `1 ≤ x` one has the pointwise tilted-term bound. -/
lemma zeta1_zero_tilted_term_le_pointwise (x : ℝ) (hx : 1 ≤ x) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (h2 : 2 ≤ ‖ρ‖) :
    ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖
      ≤ 4 * x ^ 2 * ((zeta1Order ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hre : ρ.re < 1 := zeta1_zero_re_lt_one hρ
  rw [norm_zeta1_tilt x hx0 ρ]
  have hrpos : 0 < ‖ρ‖ := by linarith
  -- `x ^ (ρ.re + 1) ≤ x ^ 2`
  have hX2 : x ^ (ρ.re + 1) ≤ x ^ 2 := by
    calc x ^ (ρ.re + 1) ≤ x ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = x ^ 2 := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- `‖ρ + 1‖ ≥ ‖ρ‖ - 1`
  have hshift : ‖ρ‖ - 1 ≤ ‖ρ + 1‖ := by
    have h := norm_add_le (ρ + 1) (-1 : ℂ)
    rw [add_neg_cancel_right, norm_neg, norm_one] at h
    linarith
  -- `1 + ‖ρ‖ ^ 2 ≤ 4 * (‖ρ‖ * ‖ρ + 1‖)`
  have hkey : 1 + ‖ρ‖ ^ 2 ≤ 4 * (‖ρ‖ * ‖ρ + 1‖) := by
    have hstep : 4 * (‖ρ‖ * (‖ρ‖ - 1)) ≤ 4 * (‖ρ‖ * ‖ρ + 1‖) := by
      have := mul_le_mul_of_nonneg_left hshift (by positivity : (0 : ℝ) ≤ 4 * ‖ρ‖)
      linarith
    have : 1 + ‖ρ‖ ^ 2 ≤ 4 * (‖ρ‖ * (‖ρ‖ - 1)) := by nlinarith [h2]
    linarith
  have hden : 0 < ‖ρ‖ * ‖ρ + 1‖ := by
    have hpos : 0 < ‖ρ + 1‖ := by linarith
    positivity
  have hden2 : 0 < 1 + ‖ρ‖ ^ 2 := by positivity
  have hmain : x ^ (ρ.re + 1) / (‖ρ‖ * ‖ρ + 1‖) ≤ 4 * x ^ 2 / (1 + ‖ρ‖ ^ 2) := by
    rw [div_le_div_iff₀ hden hden2]
    calc x ^ (ρ.re + 1) * (1 + ‖ρ‖ ^ 2)
        ≤ x ^ 2 * (4 * (‖ρ‖ * ‖ρ + 1‖)) :=
          mul_le_mul hX2 hkey (by positivity) (by positivity)
      _ = 4 * x ^ 2 * (‖ρ‖ * ‖ρ + 1‖) := by ring
  calc (zeta1Order ρ : ℝ) * x ^ (ρ.re + 1) / (‖ρ‖ * ‖ρ + 1‖)
      = (zeta1Order ρ : ℝ) * (x ^ (ρ.re + 1) / (‖ρ‖ * ‖ρ + 1‖)) := by ring
    _ ≤ (zeta1Order ρ : ℝ) * (4 * x ^ 2 / (1 + ‖ρ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
    _ = 4 * x ^ 2 * ((zeta1Order ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) := by ring

theorem zeta1_zero_tilted_term_le (x : ℝ) (hx : 1 ≤ x) :
    ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → 2 ≤ ‖ρ‖ →
      ‖(Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖
        ≤ 4 * x ^ 2 * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) := by
  intro ρ hρ h2
  exact zeta1_zero_tilted_term_le_pointwise x hx hρ h2

end Commons.NumberTheory.Zeta

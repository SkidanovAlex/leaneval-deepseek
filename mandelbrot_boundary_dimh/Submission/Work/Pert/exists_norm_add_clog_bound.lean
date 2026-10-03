import Mathlib

set_option linter.unusedVariables false

/-!
# `Work.Pert.exists_norm_add_clog_bound`

For any `a b : ℂ` and `ε > 0` there is `R` such that
`ε ≤ ‖u + a * Complex.log (-u) + b‖` for every `u` with `R ≤ ‖u‖`.

This is the elementary unboundedness statement used in the perturbation theory of
Shishikura §A: the linear term `u` dominates the logarithmic perturbation
`a * log (-u)` at infinity, so the perturbed quantity leaves every ball.

The proof bounds `‖Complex.log z‖ ≤ |log ‖z‖| + π` (the imaginary part of the
principal logarithm is the argument, of absolute value at most `π`) and uses the
little-o estimate `log = o(id)` at `+∞` to make the logarithmic term strictly
smaller than a fixed fraction of `‖u‖`.
-/

namespace Work.Pert

open Filter

/-- Bound on the principal complex logarithm: `‖log z‖ ≤ |log ‖z‖| + π`. -/
lemma norm_clog_le (z : ℂ) : ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖z‖| + |z.arg| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ |Real.log ‖z‖| + Real.pi := by
        have h := Complex.abs_arg_le_pi z
        linarith

theorem exists_norm_add_clog_bound (a b : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ u : ℂ, R ≤ ‖u‖ → ε ≤ ‖u + a * Complex.log (-u) + b‖ := by
  have hden : (0 : ℝ) < 2 * (‖a‖ + 1) := by positivity
  have hcpos : (0 : ℝ) < 1 / (2 * (‖a‖ + 1)) := by positivity
  -- `log` is eventually bounded by a fixed fraction of the identity.
  have hlogev : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x / (2 * (‖a‖ + 1)) := by
    have h := Real.isLittleO_log_id_atTop.bound hcpos
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    simp only [id_eq] at hx
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1),
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hx
    calc Real.log x ≤ (1 / (2 * (‖a‖ + 1))) * x := hx
      _ = x / (2 * (‖a‖ + 1)) := by ring
  rw [Filter.eventually_atTop] at hlogev
  obtain ⟨X, hX⟩ := hlogev
  refine ⟨max 1 (max X (2 * (‖a‖ * Real.pi + ‖b‖ + ε))), fun u hu => ?_⟩
  have hu1 : (1 : ℝ) ≤ ‖u‖ := le_trans (le_max_left _ _) hu
  have huX : X ≤ ‖u‖ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hu)
  have hu2 : 2 * (‖a‖ * Real.pi + ‖b‖ + ε) ≤ ‖u‖ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hu)
  have hA0 : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have hlogu : Real.log ‖u‖ ≤ ‖u‖ / (2 * (‖a‖ + 1)) := hX ‖u‖ huX
  have hlogφ : ‖Complex.log (-u)‖ ≤ Real.log ‖u‖ + Real.pi := by
    have h := norm_clog_le (-u)
    rw [norm_neg] at h
    rw [abs_of_nonneg (Real.log_nonneg hu1)] at h
    exact h
  have hcr : ‖a‖ / (2 * (‖a‖ + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
    nlinarith [norm_nonneg a]
  -- the logarithmic term is at most `‖u‖ / 2 + ‖a‖ * π`
  have hkey : ‖a‖ * ‖Complex.log (-u)‖ ≤ ‖u‖ / 2 + ‖a‖ * Real.pi := by
    have h1 : ‖a‖ * ‖Complex.log (-u)‖ ≤ ‖a‖ * (Real.log ‖u‖ + Real.pi) :=
      mul_le_mul_of_nonneg_left hlogφ hA0
    have h3 : ‖a‖ * Real.log ‖u‖ ≤ ‖u‖ / 2 := by
      calc ‖a‖ * Real.log ‖u‖ ≤ ‖a‖ * (‖u‖ / (2 * (‖a‖ + 1))) :=
            mul_le_mul_of_nonneg_left hlogu hA0
        _ = (‖a‖ / (2 * (‖a‖ + 1))) * ‖u‖ := by ring
        _ ≤ (1 / 2) * ‖u‖ := mul_le_mul_of_nonneg_right hcr (norm_nonneg u)
        _ = ‖u‖ / 2 := by ring
    linarith
  have htri : ‖u‖ ≤ ‖u + a * Complex.log (-u) + b‖ + ‖a * Complex.log (-u) + b‖ := by
    have h := norm_sub_le (u + a * Complex.log (-u) + b) (a * Complex.log (-u) + b)
    rw [show (u + a * Complex.log (-u) + b) - (a * Complex.log (-u) + b) = u by ring] at h
    exact h
  have h2b : ‖a * Complex.log (-u) + b‖ ≤ ‖a‖ * ‖Complex.log (-u)‖ + ‖b‖ := by
    calc ‖a * Complex.log (-u) + b‖ ≤ ‖a * Complex.log (-u)‖ + ‖b‖ := norm_add_le _ _
      _ = ‖a‖ * ‖Complex.log (-u)‖ + ‖b‖ := by rw [norm_mul]
  have hx2 : ε ≤ ‖u‖ / 2 - ‖a‖ * Real.pi - ‖b‖ := by linarith
  linarith [htri, h2b, hkey, hx2, hε]

end Work.Pert

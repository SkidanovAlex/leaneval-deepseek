import Mathlib

set_option linter.unusedVariables false

namespace Work.Parab.invOrbit

/-- For `‖z‖ ≥ 1` the complex logarithm has norm at most `log ‖z‖ + π`. -/
lemma norm_log_le_log_norm_add_pi (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  have h1 : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have hre : |Real.log ‖z‖| = Real.log ‖z‖ := abs_of_nonneg (Real.log_nonneg hz)
  have him : |z.arg| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg z), Complex.arg_le_pi z⟩
  rw [hre] at h1
  linarith

/-- Eventually `t - A * (log t + π) - B > c` (for `A ≥ 0`). -/
lemma eventually_affine_log_gt {A B c : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ t : ℝ in Filter.atTop, c < t - A * (Real.log t + Real.pi) - B := by
  have hbig : ∀ᶠ t : ℝ in Filter.atTop, (1 : ℝ) ≤ t := Filter.eventually_ge_atTop 1
  have hmul : ∀ᶠ t : ℝ in Filter.atTop, A * Real.log t ≤ t / 4 := by
    have h := (Real.isLittleO_log_id_atTop.const_mul_left A).bound
      (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [h, hbig] with t ht hbigt
    have ht' : ‖A * Real.log t‖ ≤ 1 / 4 * ‖t‖ := by simpa using ht
    have ht2 : ‖A * Real.log t‖ ≤ t / 4 := by
      have hnn : (0 : ℝ) ≤ t := by linarith
      have ht_eq : ‖t‖ = t := by rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      rw [ht_eq] at ht'
      linarith
    have hle : A * Real.log t ≤ ‖A * Real.log t‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    linarith
  have hApi : ∀ᶠ t : ℝ in Filter.atTop, A * Real.pi < t / 4 := by
    filter_upwards [Filter.eventually_gt_atTop (4 * (A * Real.pi))] with t ht
    linarith
  have hBc : ∀ᶠ t : ℝ in Filter.atTop, B + c < t / 2 := by
    filter_upwards [Filter.eventually_gt_atTop (2 * (B + c))] with t ht
    linarith
  filter_upwards [hmul, hApi, hBc] with t hmult hApit hBct
  have hAall : A * (Real.log t + Real.pi) < t / 2 := by
    rw [mul_add]
    linarith
  linarith

theorem norm_add_affine_log_eventually_gt {a b : ℂ} {c : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, ∀ w : ℂ, R < ‖w‖ → c < ‖w + a * Complex.log (-w) + b‖ := by
  set A : ℝ := ‖a‖ with hAdef
  set B : ℝ := ‖b‖ with hBdef
  have hA : 0 ≤ A := by rw [hAdef]; exact norm_nonneg a
  have hev := eventually_affine_log_gt (A := A) (B := B) (c := c) hA
  have hev1 : ∀ᶠ t : ℝ in Filter.atTop, (1 : ℝ) ≤ t := Filter.eventually_ge_atTop 1
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (hev1.and hev)
  refine ⟨R, ?_⟩
  intro w hw
  have hRle : R ≤ ‖w‖ := le_of_lt hw
  have hbig : (1 : ℝ) ≤ ‖w‖ := (hR ‖w‖ hRle).1
  have hreal : c < ‖w‖ - A * (Real.log ‖w‖ + Real.pi) - B := (hR ‖w‖ hRle).2
  have hlog : ‖Complex.log (-w)‖ ≤ Real.log ‖w‖ + Real.pi := by
    have h := norm_log_le_log_norm_add_pi (-w) (by rwa [norm_neg])
    rwa [norm_neg] at h
  have hb1 : ‖a * Complex.log (-w) + b‖ ≤ A * (Real.log ‖w‖ + Real.pi) + B := by
    calc ‖a * Complex.log (-w) + b‖ ≤ ‖a * Complex.log (-w)‖ + ‖b‖ := norm_add_le _ _
      _ = A * ‖Complex.log (-w)‖ + B := by rw [norm_mul, hAdef, hBdef]
      _ ≤ A * (Real.log ‖w‖ + Real.pi) + B := by
          have := mul_le_mul_of_nonneg_left hlog hA
          linarith
  have hb2 : ‖w‖ - ‖a * Complex.log (-w) + b‖ ≤ ‖w + a * Complex.log (-w) + b‖ := by
    have h := abs_norm_sub_norm_le w (-(a * Complex.log (-w) + b))
    rw [norm_neg] at h
    have h2 : ‖w + a * Complex.log (-w) + b‖ = ‖w - -(a * Complex.log (-w) + b)‖ := by
      congr 1
      ring
    rw [h2]
    exact le_trans (le_abs_self _) h
  linarith

end Work.Parab.invOrbit

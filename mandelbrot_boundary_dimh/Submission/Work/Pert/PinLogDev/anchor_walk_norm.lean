import Mathlib
import Submission.Work.Pert.dev_base_v3

namespace Work.Pert.PinLogDev

theorem anchor_walk_norm {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Work.Pert.Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {x : ℝ} (hR : R ≤ x) (hx1 : 1 ≤ x) :
    ‖Work.Pert.Xc d (-(x : ℂ))‖ ≤ x + ‖a‖ * Real.log x + ‖b‖ + 1 ∧
      x - ‖a‖ * Real.log x - ‖b‖ - 1 ≤ ‖Work.Pert.Xc d (-(x : ℂ))‖ := by
  -- `Xc d (-x)` is the point `Y := -x + a log x + b` up to `1/1024`; the two-sided bound on `‖Xc‖`
  -- is then the triangle inequality, using `‖log x‖ = log x` for real `x ≥ 1`.
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogC : ‖Complex.log (x : ℂ)‖ = Real.log x := by
    rw [← Complex.ofReal_log hx0.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
  have hxnorm : ‖-(x : ℂ)‖ = x := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0.le]
  set Y : ℂ := -(x : ℂ) + a * Complex.log (x : ℂ) + b with hY
  have hYnorm : ‖Y‖ ≤ x + ‖a‖ * Real.log x + ‖b‖ := by
    have h1 : ‖Y‖ ≤ ‖-(x : ℂ) + a * Complex.log (x : ℂ)‖ + ‖b‖ := by
      rw [hY]; exact norm_add_le _ _
    have h2 : ‖-(x : ℂ) + a * Complex.log (x : ℂ)‖ ≤ ‖-(x : ℂ)‖ + ‖a * Complex.log (x : ℂ)‖ :=
      norm_add_le _ _
    have h3 : ‖a * Complex.log (x : ℂ)‖ = ‖a‖ * Real.log x := by rw [norm_mul, hlogC]
    linarith [hxnorm]
  have hYnorm_lb : x - ‖a‖ * Real.log x - ‖b‖ ≤ ‖Y‖ := by
    have h1 : ‖-(x : ℂ)‖ ≤ ‖Y‖ + ‖a * Complex.log (x : ℂ) + b‖ := by
      have he : -(x : ℂ) = Y - (a * Complex.log (x : ℂ) + b) := by rw [hY]; ring
      rw [he]
      exact norm_sub_le _ _
    have h2 : ‖a * Complex.log (x : ℂ) + b‖ ≤ ‖a‖ * Real.log x + ‖b‖ := by
      have h := norm_add_le (a * Complex.log (x : ℂ)) b
      rw [norm_mul, hlogC] at h
      exact h
    linarith [hxnorm]
  have hclose : ‖Work.Pert.Xc d (-(x : ℂ)) - Y‖ ≤ 1 / 1024 := hasym x hR
  constructor
  · calc ‖Work.Pert.Xc d (-(x : ℂ))‖
        = ‖(Work.Pert.Xc d (-(x : ℂ)) - Y) + Y‖ := by rw [sub_add_cancel]
      _ ≤ ‖Work.Pert.Xc d (-(x : ℂ)) - Y‖ + ‖Y‖ := norm_add_le _ _
      _ ≤ 1 / 1024 + (x + ‖a‖ * Real.log x + ‖b‖) := add_le_add hclose hYnorm
      _ ≤ x + ‖a‖ * Real.log x + ‖b‖ + 1 := by linarith
  · have h2 : ‖Y‖ ≤ ‖Work.Pert.Xc d (-(x : ℂ))‖ + 1 / 1024 := by
      have he : Y = (Y - Work.Pert.Xc d (-(x : ℂ))) + Work.Pert.Xc d (-(x : ℂ)) := by ring
      have hnorm : ‖Y‖ = ‖(Y - Work.Pert.Xc d (-(x : ℂ))) + Work.Pert.Xc d (-(x : ℂ))‖ :=
        congrArg (fun z : ℂ => ‖z‖) he
      rw [hnorm]
      calc ‖(Y - Work.Pert.Xc d (-(x : ℂ))) + Work.Pert.Xc d (-(x : ℂ))‖
          ≤ ‖Y - Work.Pert.Xc d (-(x : ℂ))‖ + ‖Work.Pert.Xc d (-(x : ℂ))‖ := norm_add_le _ _
        _ = ‖Work.Pert.Xc d (-(x : ℂ)) - Y‖ + ‖Work.Pert.Xc d (-(x : ℂ))‖ := by rw [norm_sub_rev]
        _ ≤ 1 / 1024 + ‖Work.Pert.Xc d (-(x : ℂ))‖ := by linarith
        _ = ‖Work.Pert.Xc d (-(x : ℂ))‖ + 1 / 1024 := by ring
    linarith

end Work.Pert.PinLogDev

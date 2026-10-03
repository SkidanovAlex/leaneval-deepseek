import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.PinLogDev.AxisAux.log_sub_log_norm_le
import Submission.Work.Pert.PinLogDev.AxisAux.norm_sub_le_of_mem_ball_deriv
import Submission.Work.Pert.PinLogDev.AxisAux.axis_arith

/-!
# `deltaF_axis_le`: the defect of the lifted map on the axis `w = i s`

For a perturbation `f z = z + z (z - σ) u z` in `𝓕₁` with multiplier data
`σ`, `α` (`1 - σ u 0 = exp (2πi α)`, `InF1 α`, `‖α‖ ≤ 1/64`) and `s ≥ 3`, the lift
`F = liftF u σ α` of `f` satisfies, on the axis `w = i s`,

  `‖F (i s) - (i s + 1)‖ ≤ Kd / s`.

Since `F w = w + (2πiα)⁻¹ log (1 - sfun u σ α w)`, this is the statement
`‖log (1 - sfun (i s)) - log (1 - σ u 0)‖ ≤ Kd ‖2πiα‖ / s`, i.e. the defect of `F` decays like
`1/|w|` along the axis.  The mechanism:

* `τ = τ_f (i s) = σ / (1 - exp (2π s α))` and `InF1 α` gives `Re α ≥ 0.7 ‖α‖`, hence
  `‖1 - exp (2π s α)‖ ≥ Re (2π s α) ≥ 0.7 s ‖2πiα‖`, so `‖τ‖ ≤ 1.9/s`;
* `1 - σ u 0 = exp (2πiα)` gives `σ = (1 - exp (2πiα))/u 0`, so `‖σ‖ ≤ 1.3 ‖2πiα‖`;
* hence `‖τ‖‖u τ‖ ≤ 1.9/s · 9/8` stays `≤ 0.29`, so `‖1 + τ u τ‖ ≥ 7/25`, and both
  `1 - sfun = σ u τ/(1 + τ u τ)` and `1 - σ u 0` lie in the ball of radius `3/4` about `1`;
* `‖u τ - u 0‖ ≤ (4/rr)‖τ‖` (Schwarz lemma, from `‖u‖ ≤ 2` on `ball 0 rr`);
* the algebra `(1 - sfun) - (1 - σu 0) = σ ((u 0 - u τ) + u 0 τ u τ)/(1 + τ u τ)` then gives
  `‖(1 - sfun) - (1 - σ u 0)‖ = O(‖2πiα‖/s)`, and the principal logarithm is `4`-Lipschitz on
  the ball of radius `3/4` about `1`.
-/

namespace Work.Pert.PinLogDev

open MandelDim Complex
open Work.Pert.PinLogDev.AxisAux

/-! ## The estimate -/

/-- `u ↦ e^u - 1 - u` is nonnegative on `ℝ`, so the "axis" defect `1 - e^w` always dominates
`Re w`. -/
theorem re_le_norm_one_sub_exp (w : ℂ) : w.re ≤ ‖1 - Complex.exp w‖ := by
  have h1 : ‖Complex.exp w‖ - ‖(1 : ℂ)‖ ≤ ‖Complex.exp w - 1‖ :=
    (le_abs_self _).trans (abs_norm_sub_norm_le _ _)
  have h2 : ‖Complex.exp w - 1‖ = ‖1 - Complex.exp w‖ := norm_sub_rev _ _
  have h3 : ‖Complex.exp w‖ - ‖(1 : ℂ)‖ = Real.exp w.re - 1 := by
    rw [Complex.norm_exp]; simp
  have h4 : w.re ≤ Real.exp w.re - 1 := by
    have := Real.add_one_le_exp w.re
    linarith
  linarith [h1, h2, h3, h4]

/-- `-(2πi α (s i)) = 2π s α`: the argument of the exponential at the axis point `w = i s`. -/
theorem axis_arg (α : ℂ) (s : ℝ) :
    -(2 * Real.pi * I * α * ((s : ℂ) * I)) = 2 * Real.pi * (s : ℂ) * α := by
  have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
  linear_combination (-(2 * Real.pi * (s : ℂ) * α)) * hI

/-- `log (exp (2πiα)) = 2πiα` for `α` in `𝓕₁` with `‖α‖ ≤ 1/64` (the imaginary part of `2πiα`
lies in `(0, π]`). -/
theorem log_exp_axis {α : ℂ} (hre : 0 < α.re) (hα : ‖α‖ ≤ 1 / 64) :
    Complex.log (Complex.exp (2 * Real.pi * I * α)) = 2 * Real.pi * I * α := by
  have him : (2 * Real.pi * I * α).im = 2 * Real.pi * α.re := by simp [Complex.mul_im]
  refine Complex.log_exp ?_ ?_
  · rw [him]
    have h2 : 0 < 2 * Real.pi * α.re := mul_pos (by positivity) hre
    linarith [Real.pi_pos]
  · rw [him]
    have h2 : 2 * Real.pi * α.re ≤ 2 * Real.pi * (1 / 64) := by
      have hre_le : α.re ≤ ‖α‖ := Complex.re_le_norm α
      have h2a : 2 * Real.pi * α.re ≤ 2 * Real.pi * ‖α‖ :=
        mul_le_mul_of_nonneg_left hre_le (by positivity)
      have h2b : 2 * Real.pi * ‖α‖ ≤ 2 * Real.pi * (1 / 64) :=
        mul_le_mul_of_nonneg_left hα (by positivity)
      linarith
    have h3 : 2 * Real.pi * (1 / 64) ≤ Real.pi := by linarith [Real.pi_pos]
    linarith

/-- The defect of the lift on the axis: `F w - (w + 1) = (2πiα)⁻¹ (log (1 - sfun w) - log Q)`
with `Q = 1 - σ u 0`. -/
theorem liftF_sub_eq {u : ℂ → ℂ} {σ α w : ℂ} (hα : α ≠ 0)
    (h : Complex.log (1 - σ * u 0) = 2 * Real.pi * I * α) :
    Work.Pert.liftF u σ α w - (w + 1)
      = (1 / (2 * Real.pi * I * α))
        * (Complex.log (1 - Work.Pert.sfun u σ α w) - Complex.log (1 - σ * u 0)) := by
  have hZne : (2 * Real.pi * I * α) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hα]
  rw [Work.Pert.liftF, h]
  field_simp
  ring

/-- `(1/ε) (C ε / s) = C/s`: cancelling the norm of `2πiα`. -/
theorem inv_mul_div_cancel (ε s C : ℝ) (hε : ε ≠ 0) : (1 / ε) * (C * ε / s) = C / s := by
  field_simp

theorem deltaF_axis_le (rr : ℝ) (hrr : 0 < rr) (a : ℂ) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧
      ∀ {u : ℂ → ℂ} {σ α : ℂ} {s : ℝ},
      3 ≤ s → MandelDim.InF1 α → ‖α‖ ≤ 1 / 64 →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      ‖u 0 - 1‖ ≤ 1 / 8 → ‖deriv u 0 + a‖ ≤ 1 / 8 →
      Work.Pert.tauC σ α ((s : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) rr →
      ‖u (Work.Pert.tauC σ α ((s : ℂ) * Complex.I)) - 1‖ ≤ 1 / 8 →
      ‖Work.Pert.liftF u σ α ((s : ℂ) * Complex.I) - ((s : ℂ) * Complex.I + 1)‖ ≤ Kd / s := by
  refine ⟨200 / rr + 100, by positivity, ?_⟩
  intro u σ α s hs3 hInF1 hα64 huD huB hnorm hdu0 hder hmem htau
  -- ## real part of `α`
  have hre_pos : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hαne : α ≠ 0 := by
    rintro rfl
    simp at hre_pos
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hs0 : 0 < s := by linarith
  -- ## `‖2πiα‖`
  have hZnorm : ‖2 * Real.pi * I * α‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I]
  have hZpos : 0 < ‖2 * Real.pi * I * α‖ := by rw [hZnorm]; positivity
  have hε1 : ‖2 * Real.pi * I * α‖ ≤ 1 / 8 := by
    rw [hZnorm]; nlinarith [Real.pi_lt_four, Real.pi_pos, hα64]
  -- ## `Re α ≥ 0.7 ‖α‖` (from `InF1`)
  have hre_ge : (7 / 10) * ‖α‖ ≤ α.re := by
    have hsq : α.im ^ 2 < α.re ^ 2 := by
      have h1 : α.im < α.re := (abs_lt.mp hInF1).2
      have h2 : -α.re < α.im := (abs_lt.mp hInF1).1
      nlinarith [mul_pos (sub_pos.mpr h1) (by linarith : (0 : ℝ) < α.re + α.im)]
    have h2 : ‖α‖ ^ 2 < 2 * α.re ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hsq]
    have h3 : ((7 / 10) * ‖α‖) ^ 2 < α.re ^ 2 := by nlinarith [h2, hre_pos]
    have h4 : |(7 / 10) * ‖α‖| < |α.re| := sq_lt_sq.mp h3
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (le_of_lt hre_pos)] at h4
    linarith
  -- ## the axis bound `‖1 - exp (2π s α)‖ ≥ 0.7 s ‖2πiα‖`
  have haxis : (7 / 10) * s * ‖2 * Real.pi * I * α‖
      ≤ ‖1 - Complex.exp (2 * Real.pi * (s : ℂ) * α)‖ := by
    have h0 := re_le_norm_one_sub_exp (2 * Real.pi * (s : ℂ) * α)
    have h1 : (2 * Real.pi * (s : ℂ) * α).re = 2 * Real.pi * s * α.re := by
      simp [Complex.mul_re]
    rw [h1] at h0
    have h2 : (7 / 10) * s * ‖2 * Real.pi * I * α‖ ≤ 2 * Real.pi * s * α.re := by
      rw [hZnorm]
      have hmul := mul_le_mul_of_nonneg_left hre_ge (by positivity : (0 : ℝ) ≤ 2 * Real.pi * s)
      linarith [hmul]
    linarith
  have hden_pos : 0 < ‖1 - Complex.exp (2 * Real.pi * (s : ℂ) * α)‖ := by
    have h : 0 < (7 / 10) * s * ‖2 * Real.pi * I * α‖ :=
      mul_pos (mul_pos (by norm_num) hs0) hZpos
    linarith
  -- ## `σ` and the basic normalisation
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * I * α) := by
    linear_combination -hnorm
  have hexp_le : ‖1 - Complex.exp (2 * Real.pi * I * α)‖ ≤ 9 / 8 * ‖2 * Real.pi * I * α‖ := by
    have hbase := Complex.norm_exp_sub_one_sub_id_le (x := 2 * Real.pi * I * α)
      (by linarith [hε1] : ‖2 * Real.pi * I * α‖ ≤ 1)
    have htri : ‖Complex.exp (2 * Real.pi * I * α) - 1 - 2 * Real.pi * I * α‖
        + ‖2 * Real.pi * I * α‖
        ≥ ‖Complex.exp (2 * Real.pi * I * α) - 1‖ := by
      have h := norm_add_le (Complex.exp (2 * Real.pi * I * α) - 1 - 2 * Real.pi * I * α)
        (2 * Real.pi * I * α)
      have heq : Complex.exp (2 * Real.pi * I * α) - 1 - 2 * Real.pi * I * α
          + 2 * Real.pi * I * α = Complex.exp (2 * Real.pi * I * α) - 1 := by ring
      rwa [heq] at h
    have hsq : ‖2 * Real.pi * I * α‖ ^ 2 ≤ 1 / 8 * ‖2 * Real.pi * I * α‖ := by
      nlinarith [hε1, norm_nonneg (2 * Real.pi * I * α)]
    rw [norm_sub_rev]
    linarith
  have hu0_low : (7 / 8 : ℝ) ≤ ‖u 0‖ := by
    have h := abs_norm_sub_norm_le (u 0) (1 : ℂ)
    simp only [norm_one] at h
    have h2 := neg_le_abs (‖u 0‖ - 1)
    linarith
  have hu0_up : ‖u 0‖ ≤ 9 / 8 := by
    have h1 : (u 0 - 1) + 1 = u 0 := by ring
    rw [← h1]
    have h2 := norm_add_le (u 0 - 1) (1 : ℂ)
    simp only [norm_one] at h2
    linarith
  have hσ_le : ‖σ‖ ≤ 13 / 10 * ‖2 * Real.pi * I * α‖ := by
    have hmul : ‖σ‖ * ‖u 0‖ = ‖1 - Complex.exp (2 * Real.pi * I * α)‖ := by
      rw [← norm_mul, hσu]
    nlinarith [hmul, hexp_le, hu0_low, norm_nonneg σ]
  -- ## `τ = τ_f (i s) = σ/(1 - exp (2π s α))`
  set τ : ℂ := Work.Pert.tauC σ α ((s : ℂ) * Complex.I) with hτdef
  have hτ_eq : τ = σ / (1 - Complex.exp (2 * Real.pi * (s : ℂ) * α)) := by
    rw [hτdef, Work.Pert.tauC, axis_arg]
  have hτnorm : ‖τ‖ = ‖σ‖ / ‖1 - Complex.exp (2 * Real.pi * (s : ℂ) * α)‖ := by
    rw [hτ_eq, norm_div]
  have hτ_le : ‖τ‖ ≤ 19 / 10 / s := by
    rw [hτnorm, div_le_div_iff₀ hden_pos hs0]
    have h1 : ‖σ‖ * s ≤ 13 / 10 * ‖2 * Real.pi * I * α‖ * s :=
      mul_le_mul_of_nonneg_right hσ_le hs0.le
    have h2 : 19 / 10 * ((7 / 10) * s * ‖2 * Real.pi * I * α‖)
        ≤ 19 / 10 * ‖1 - Complex.exp (2 * Real.pi * (s : ℂ) * α)‖ :=
      mul_le_mul_of_nonneg_left haxis (by norm_num)
    nlinarith [h1, h2, hZpos.le, hs0.le]
  have hv_le : ‖u τ‖ ≤ 9 / 8 := by
    have h1 : (u τ - 1) + 1 = u τ := by ring
    rw [← h1]
    have h2 := norm_add_le (u τ - 1) (1 : ℂ)
    simp only [norm_one] at h2
    linarith
  -- ## the denominator `1 + τ u τ`
  have hτv_le : ‖τ‖ * ‖u τ‖ ≤ 171 / 80 / s := by
    have h1 : ‖τ‖ * ‖u τ‖ ≤ 19 / 10 / s * (9 / 8) :=
      mul_le_mul hτ_le hv_le (norm_nonneg _) (by positivity)
    calc ‖τ‖ * ‖u τ‖ ≤ 19 / 10 / s * (9 / 8) := h1
      _ = 171 / 80 / s := by ring
  have h1τv : (7 / 25 : ℝ) ≤ ‖1 + τ * u τ‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
    have h2 : ‖-(τ * u τ)‖ = ‖τ‖ * ‖u τ‖ := by rw [norm_neg, norm_mul]
    rw [norm_one, h2] at h
    have h3 : 1 - -(τ * u τ) = 1 + τ * u τ := by ring
    rw [h3] at h
    have h5 : (1 : ℝ) - ‖τ‖ * ‖u τ‖ ≤ |1 - ‖τ‖ * ‖u τ‖| := le_abs_self _
    have h6 : (7 / 25 : ℝ) ≤ 1 - 171 / 80 / s := by
      have h7 : 171 / 80 / s ≤ 18 / 25 := by
        rw [div_le_iff₀ hs0]
        nlinarith [hs3]
      linarith
    linarith [h, h5, h6, hτv_le]
  have h1τv_ne : 1 + τ * u τ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1τv
    norm_num at h1τv
  -- ## `sfun` at `i s`
  have hsfun : Work.Pert.sfun u σ α ((s : ℂ) * Complex.I) = σ * u τ / (1 + τ * u τ) := by
    simp only [Work.Pert.sfun]
    rw [← hτdef]
  have hPsubQ : (1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I)) - (1 - σ * u 0)
      = σ * ((u 0 - u τ) + u 0 * (τ * u τ)) / (1 + τ * u τ) := by
    have hden : (1 + u τ * τ) ≠ 0 := by simpa only [mul_comm (u τ) τ] using h1τv_ne
    rw [hsfun]
    field_simp
    ring
  -- ## `P` and `Q` in the ball of radius `3/4` about `1`
  have hmul_le : ‖u 0 * (τ * u τ)‖ ≤ 9 / 8 * (9 / 8 * ‖τ‖) := by
    rw [norm_mul, norm_mul]
    have h1 : ‖u 0‖ * ‖u τ‖ ≤ 9 / 8 * (9 / 8) :=
      mul_le_mul hu0_up hv_le (norm_nonneg _) (by norm_num)
    calc ‖u 0‖ * (‖τ‖ * ‖u τ‖) = (‖u 0‖ * ‖u τ‖) * ‖τ‖ := by ring
      _ ≤ 9 / 8 * (9 / 8) * ‖τ‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg τ)
      _ = 9 / 8 * (9 / 8 * ‖τ‖) := by ring
  have hP1 : ‖(1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I)) - 1‖ ≤ 3 / 4 := by
    have h1 : (1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I)) - 1
        = - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I) := by ring
    rw [h1, norm_neg, hsfun, norm_div, norm_mul]
    have h2 : ‖σ‖ * ‖u τ‖ ≤ 13 / 10 * ‖2 * Real.pi * I * α‖ * (9 / 8) :=
      mul_le_mul hσ_le hv_le (norm_nonneg _) (by positivity)
    have h3 : ‖σ‖ * ‖u τ‖ / (7 / 25) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 7 / 25)]
      nlinarith [h2, hε1, hZpos.le]
    calc ‖σ‖ * ‖u τ‖ / ‖1 + τ * u τ‖
        ≤ ‖σ‖ * ‖u τ‖ / (7 / 25) := div_le_div_of_nonneg_left (by positivity) (by norm_num) h1τv
      _ ≤ 3 / 4 := h3
  have hQ1 : ‖(1 - σ * u 0) - 1‖ ≤ 3 / 4 := by
    have h1 : (1 - σ * u 0) - 1 = - (σ * u 0) := by ring
    rw [h1, norm_neg, norm_mul]
    nlinarith [mul_le_mul hσ_le hu0_up (norm_nonneg _) (by positivity), hε1, hZpos.le]
  -- ## the logarithm estimate
  have hPQ_le : ‖(1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I)) - (1 - σ * u 0)‖
      ≤ ‖σ‖ * (4 * ‖τ‖ / rr + 9 / 8 * (9 / 8 * ‖τ‖)) / (7 / 25) := by
    rw [hPsubQ, norm_div, norm_mul]
    have hd : ‖u 0 - u τ‖ ≤ 4 * ‖τ‖ / rr := by
      have h := norm_sub_le_of_mem_ball_deriv hrr huD (fun z hz => (huB z hz).2) hdu0 hmem
      rw [norm_sub_rev]
      calc ‖u τ - u 0‖ ≤ (4 / rr) * ‖τ‖ := h
        _ = 4 * ‖τ‖ / rr := by ring
    have hnum : ‖(u 0 - u τ) + u 0 * (τ * u τ)‖ ≤ 4 * ‖τ‖ / rr + 9 / 8 * (9 / 8 * ‖τ‖) := by
      calc ‖(u 0 - u τ) + u 0 * (τ * u τ)‖ ≤ ‖u 0 - u τ‖ + ‖u 0 * (τ * u τ)‖ := norm_add_le _ _
        _ ≤ 4 * ‖τ‖ / rr + 9 / 8 * (9 / 8 * ‖τ‖) := add_le_add hd hmul_le
    have h1 : ‖σ‖ * ‖(u 0 - u τ) + u 0 * (τ * u τ)‖
        ≤ ‖σ‖ * (4 * ‖τ‖ / rr + 9 / 8 * (9 / 8 * ‖τ‖)) :=
      mul_le_mul_of_nonneg_left hnum (norm_nonneg σ)
    calc ‖σ‖ * ‖(u 0 - u τ) + u 0 * (τ * u τ)‖ / ‖1 + τ * u τ‖
        ≤ ‖σ‖ * (4 * ‖τ‖ / rr + 9 / 8 * (9 / 8 * ‖τ‖)) / ‖1 + τ * u τ‖ :=
          div_le_div_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ ‖σ‖ * (4 * ‖τ‖ / rr + 9 / 8 * (9 / 8 * ‖τ‖)) / (7 / 25) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) h1τv
  have hlog_le : ‖Complex.log (1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I))
        - Complex.log (1 - σ * u 0)‖
      ≤ 4 * (‖σ‖ * (4 * ‖τ‖ / rr + 9 / 8 * (9 / 8 * ‖τ‖)) / (7 / 25)) := by
    have h := log_sub_log_norm_le hP1 hQ1
    calc _ ≤ 4 * ‖(1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I)) - (1 - σ * u 0)‖ := h
      _ ≤ 4 * (‖σ‖ * (4 * ‖τ‖ / rr + 9 / 8 * (9 / 8 * ‖τ‖)) / (7 / 25)) :=
          mul_le_mul_of_nonneg_left hPQ_le (by norm_num)
  have harith := axis_arith hrr hs3 hZpos (norm_nonneg σ) (norm_nonneg τ) hσ_le hτ_le
  have hmain : ‖Complex.log (1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I))
        - Complex.log (1 - σ * u 0)‖ ≤ (200 / rr + 100) * ‖2 * Real.pi * I * α‖ / s :=
    le_trans hlog_le harith
  -- ## the value of `log (1 - σ u 0)`
  have hlogQ : Complex.log (1 - σ * u 0) = 2 * Real.pi * I * α := by
    rw [hnorm]
    exact log_exp_axis hre_pos hα64
  -- ## rewriting the goal
  rw [liftF_sub_eq hαne hlogQ, norm_mul, norm_div, norm_one]
  have hfin : (1 / ‖2 * Real.pi * I * α‖)
        * ‖Complex.log (1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I))
          - Complex.log (1 - σ * u 0)‖ ≤ (200 / rr + 100) / s := by
    have h1 : (1 / ‖2 * Real.pi * I * α‖)
          * ‖Complex.log (1 - Work.Pert.sfun u σ α ((s : ℂ) * Complex.I))
            - Complex.log (1 - σ * u 0)‖
        ≤ (1 / ‖2 * Real.pi * I * α‖)
          * ((200 / rr + 100) * ‖2 * Real.pi * I * α‖ / s) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    exact inv_mul_div_cancel _ s _ (ne_of_gt hZpos)
  exact hfin

end Work.Pert.PinLogDev

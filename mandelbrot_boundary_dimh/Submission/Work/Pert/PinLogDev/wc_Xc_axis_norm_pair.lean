import Mathlib
import Submission.Work.Pert.PinLogDev.AnchorWalk
import Submission.Work.Pert.PinLogDev.anchor_walk
import Submission.Work.Pert.Ksub2.Setup

set_option linter.unusedVariables false

/-!
# `Work.Pert.PinLogDev.wc_Xc_axis_norm_pair`

Two size estimates for the datum's axis point `w = Xc d (-x) = τ₀ (φ₀ (-x))`, obtained from the
asymptotic `‖Xc d (-x) - (-x + a log x + b)‖ ≤ 1/1024` (the datum-level asymptotic of
`exists_Xc_axis_asym`) together with the arithmetic hypotheses on `a`, `b`, `x`, `M`, `α`:

* `64 ≤ ‖w‖` — the axis point is bounded away from `0`.  Indeed, writing
  `Y := -x + a log x + b`, the reverse triangle inequality gives
  `‖w‖ ≥ ‖Y‖ - 1/1024 ≥ x - ‖a‖ log x - ‖b‖ - 1/1024`, and
  `‖a‖ log x ≤ x/4` (`mul_log_le_div`, from `64 ‖a‖² ≤ x`, `x ≥ 1`) while
  `‖b‖ ≤ 3x/4 - 65`; the lower bound is `65 - 1/1024 > 64`.

* `‖α‖ ‖w‖ ≤ 2/3` — the rotation factor is small.  From `‖w‖ ≤ x + ‖a‖ log x + ‖b‖ + 1/1024`
  with `x ≤ M`, `‖a‖ log x ≤ M/4` (again `mul_log_le_div`, from `64 ‖a‖² ≤ M`, `M ≥ 1`) and
  `‖b‖ ≤ M/12 - 1` one gets `‖w‖ ≤ 4M/3`, and `‖α‖ M ≤ 1/2` gives `‖α‖ ≤ 1/(2M)`, whence
  `‖α‖ ‖w‖ ≤ (1/(2M)) · (4M/3) = 2/3`.

Only the asymptotic hypothesis on the curve is used (`d` enters solely through it); the two
conclusions are pure real-arithmetic consequences of the hypotheses.  The hypothesis `haX` is
not needed (kept for compatibility with the caller).
-/

namespace Work.Pert.PinLogDev

/-- Reverse triangle inequality in the form `‖u‖ - ‖v‖ ≤ ‖u + v‖`. -/
private theorem norm_add_rev {E : Type*} [NormedAddCommGroup E] (u v : E) :
    ‖u‖ - ‖v‖ ≤ ‖u + v‖ := by
  have h := norm_sub_norm_le u (-v)
  simpa using h

theorem wc_Xc_axis_norm_pair {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Work.Pert.Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {α : ℂ} {x M : ℝ} (hRx : R ≤ x) (hx1 : 1 ≤ x) (hxM : x ≤ M)
    (haX : ‖a‖ ≤ x) (h64x : 64 * ‖a‖ ^ 2 ≤ x) (hbx : ‖b‖ + 65 ≤ 3 * x / 4)
    (hM1 : 1 ≤ M) (hαM : ‖α‖ * M ≤ 1 / 2)
    (h64M : 64 * ‖a‖ ^ 2 ≤ M) (hbM : 12 * (‖b‖ + 1) ≤ M) :
    64 ≤ ‖Work.Pert.Xc d (-(x : ℂ))‖ ∧ ‖α‖ * ‖Work.Pert.Xc d (-(x : ℂ))‖ ≤ 2 / 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  -- the model point `Y = -x + a log x + b` and its distance to `w`
  set w : ℂ := Work.Pert.Xc d (-(x : ℂ)) with hw
  set Y : ℂ := -(x : ℂ) + a * Complex.log (x : ℂ) + b with hY
  have hclose : ‖w - Y‖ ≤ 1 / 1024 := hasym x hRx
  -- `Complex.log` of a positive real
  have hlogC : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx0.le).symm
  have hYeq : Y = -(x : ℂ) + a * (Real.log x : ℂ) + b := by rw [hY, hlogC]
  have hnormx : ‖-(x : ℂ)‖ = x := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0.le]
  have hnA : ‖a * (Real.log x : ℂ)‖ = ‖a‖ * Real.log x := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
  have hAbeq : ‖a * (Real.log x : ℂ) + b‖ ≤ ‖a‖ * Real.log x + ‖b‖ := by
    have h := norm_add_le (a * (Real.log x : ℂ)) b
    rwa [hnA] at h
  have hsplit : -(x : ℂ) + a * (Real.log x : ℂ) + b
      = -(x : ℂ) + (a * (Real.log x : ℂ) + b) := by ring
  -- two-sided estimate of `‖Y‖`
  have hYlow : x - ‖a‖ * Real.log x - ‖b‖ ≤ ‖Y‖ := by
    rw [hYeq, hsplit]
    have h1 : ‖-(x : ℂ)‖ - ‖a * (Real.log x : ℂ) + b‖
        ≤ ‖-(x : ℂ) + (a * (Real.log x : ℂ) + b)‖ :=
      norm_add_rev (-(x : ℂ)) (a * (Real.log x : ℂ) + b)
    rw [hnormx] at h1
    linarith
  have hYup : ‖Y‖ ≤ x + ‖a‖ * Real.log x + ‖b‖ := by
    rw [hYeq, hsplit]
    have h1 : ‖-(x : ℂ) + (a * (Real.log x : ℂ) + b)‖
        ≤ ‖-(x : ℂ)‖ + ‖a * (Real.log x : ℂ) + b‖ := norm_add_le _ _
    rw [hnormx] at h1
    linarith
  -- `‖w‖` against `‖Y‖`
  have hw_low : ‖Y‖ - ‖w - Y‖ ≤ ‖w‖ := by
    have h := norm_add_rev Y (w - Y)
    rw [show Y + (w - Y) = w from by ring] at h
    exact h
  have hw_up : ‖w‖ - ‖Y‖ ≤ ‖w - Y‖ := norm_sub_norm_le w Y
  -- the two arithmetic inputs (`mul_log_le_div` is `Work.Pert.PinLogDev.mul_log_le_div`)
  have h4 : ‖a‖ * Real.log x ≤ x / 4 := mul_log_le_div (norm_nonneg a) hx1 h64x
  have h4M : ‖a‖ * Real.log x ≤ M / 4 := by linarith [h4, hxM]
  have hbn : ‖b‖ ≤ 3 * x / 4 - 65 := by linarith
  have hbM' : ‖b‖ ≤ M / 12 - 1 := by linarith
  constructor
  · -- `64 ≤ ‖w‖`
    linarith [hw_low, hclose, hYlow, h4, hbn]
  · -- `‖α‖ ‖w‖ ≤ 2/3`
    have hwle : ‖w‖ ≤ 4 * M / 3 := by linarith [hw_up, hclose, hYup, h4M, hbM', hxM]
    have hαle : ‖α‖ ≤ 1 / (2 * M) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hαM]
    have hfin : ‖α‖ * ‖w‖ ≤ (1 / (2 * M)) * (4 * M / 3) :=
      mul_le_mul hαle hwle (norm_nonneg w) (by positivity)
    have hsimp : (1 / (2 * M)) * (4 * M / 3) = 2 / 3 := by
      field_simp
      norm_num
    rw [hsimp] at hfin
    exact hfin

end Work.Pert.PinLogDev

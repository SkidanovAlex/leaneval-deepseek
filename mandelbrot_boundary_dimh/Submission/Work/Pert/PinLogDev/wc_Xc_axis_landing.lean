import Mathlib
import Submission.Work.Pert.PinLogDev.AnchorWalk
import Submission.Work.Pert.Ksub2.Setup

namespace Work.Pert.PinLogDev

theorem wc_Xc_axis_landing {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Work.Pert.Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {x : ℝ} (hR : R ≤ x) (hx1 : 1 ≤ x) :
    ‖Work.Pert.Xc d (-(x : ℂ)) + (x : ℂ)‖ ≤ ‖a‖ * Real.log x + ‖b‖ + 1 ∧
      (Work.Pert.Xc d (-(x : ℂ))).re ≤ -x + (|a.re| + |a.im|) * Real.log x
          + ((|a.re| + |a.im|) * Real.pi + |b.re| + 1) := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hlogx : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  -- `log` of a nonnegative real is the real logarithm, so `‖log x‖ = Real.log x`.
  have hlog : Complex.log (x:ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx0).symm
  have hnorma : ‖Complex.log (x:ℂ)‖ = Real.log x := by
    rw [hlog]; simp [abs_of_nonneg hlogx]
  have hdev := hasym x hR
  have hLre : (-(x:ℂ) + a * Complex.log (x:ℂ) + b).re = -x + a.re * Real.log x + b.re := by
    rw [hlog]; simp
  constructor
  · -- First conjunct: undo the `- x` by triangle inequality.
    have h1 : ‖a * Complex.log (x:ℂ) + b‖ ≤ ‖a‖ * Real.log x + ‖b‖ := by
      calc ‖a * Complex.log (x:ℂ) + b‖ ≤ ‖a * Complex.log (x:ℂ)‖ + ‖b‖ := norm_add_le _ _
        _ = ‖a‖ * ‖Complex.log (x:ℂ)‖ + ‖b‖ := by rw [norm_mul]
        _ = ‖a‖ * Real.log x + ‖b‖ := by rw [hnorma]
    have hsplit : Work.Pert.Xc d (-(x:ℂ)) + (x:ℂ)
        = (Work.Pert.Xc d (-(x:ℂ)) - (-(x:ℂ) + a * Complex.log (x:ℂ) + b))
          + (a * Complex.log (x:ℂ) + b) := by ring
    rw [hsplit]
    have h2 := norm_add_le (Work.Pert.Xc d (-(x:ℂ)) - (-(x:ℂ) + a * Complex.log (x:ℂ) + b))
      (a * Complex.log (x:ℂ) + b)
    linarith
  · -- Second conjunct: split off the error term and take real parts.
    have hAeq : Work.Pert.Xc d (-(x:ℂ))
        = (Work.Pert.Xc d (-(x:ℂ)) - (-(x:ℂ) + a * Complex.log (x:ℂ) + b))
          + (-(x:ℂ) + a * Complex.log (x:ℂ) + b) := by ring
    have hre1 : (Work.Pert.Xc d (-(x:ℂ))).re
        = (Work.Pert.Xc d (-(x:ℂ)) - (-(x:ℂ) + a * Complex.log (x:ℂ) + b)).re
          + (-(x:ℂ) + a * Complex.log (x:ℂ) + b).re := by
      have := congrArg Complex.re hAeq
      rwa [Complex.add_re] at this
    rw [hre1, hLre]
    have hd : (Work.Pert.Xc d (-(x:ℂ)) - (-(x:ℂ) + a * Complex.log (x:ℂ) + b)).re ≤ 1/1024 :=
      le_trans (Complex.re_le_norm _) hdev
    have ha : a.re ≤ |a.re| := le_abs_self _
    have hb : b.re ≤ |b.re| := le_abs_self _
    have h1 : a.re * Real.log x ≤ |a.re| * Real.log x := mul_le_mul_of_nonneg_right ha hlogx
    have h2 : |a.re| * Real.log x ≤ (|a.re| + |a.im|) * Real.log x :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hlogx
    have h3 : (0:ℝ) ≤ (|a.re| + |a.im|) * Real.pi :=
      mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) Real.pi_pos.le
    linarith

end Work.Pert.PinLogDev

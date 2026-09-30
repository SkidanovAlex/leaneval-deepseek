import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.est_Theta_yu

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # BW §13: the `log`-form estimate for `Θ(x;k,l,m)` at a rational point

Given `est_Theta_yu`, `‖Θ(z;k,l,m)‖ ≤ (e(1 + ‖z‖/k))^{kl}`, we deduce the multiplicative
form of the same bound, in which the linear growth in `|x|` is absorbed into a freely chosen
`μ ≥ 1`:
`log|Θ(x;k,l,m)| ≤ kl·(1 + log μ + 1/μ) + l·|x|/μ`.
The only ingredients are `log(1+u) ≤ log μ + u/μ` (from `log v ≤ v - 1`) and the passage
`log((e(1+t/k))^{kl}) = kl·(1 + log(1+t/k))`. -/

namespace Work.BW

/-- `Θ` at a rational point is the cast to `ℂ` of `thetaRatQ`. -/
private lemma thetaRatQ_cast (x : ℚ) (k l m : ℕ) :
    Theta (x : ℂ) k l m = ((thetaRatQ x k l m : ℚ) : ℂ) := by
  simp only [Theta, thetaRatQ]
  rw [show (x : ℂ) = (Algebra.ofId ℚ ℂ) x by simp]
  exact Polynomial.aeval_algHom_apply (Algebra.ofId ℚ ℂ) x _

/-- The elementary `μ`-inequality: `log (1+u) ≤ log μ + u/μ` for `u ≥ 0`, `μ ≥ 1`.
It follows from `log v ≤ v - 1` applied to `v = (1+u)/μ`, since `(1+u)/μ - 1 ≤ u/μ`. -/
private lemma log_one_add_le_log_mu_add (u μ : ℝ) (hu : 0 ≤ u) (hμ : 1 ≤ μ) :
    Real.log (1 + u) ≤ Real.log μ + u / μ := by
  have hμpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have h1 : (0 : ℝ) < (1 + u) / μ := by positivity
  have h2 : 1 / μ ≤ 1 := by
    rw [div_le_one hμpos]; exact hμ
  have h3 : (1 + u) / μ = 1 / μ + u / μ := by ring
  calc Real.log (1 + u)
      = Real.log ((1 + u) / μ * μ) := by rw [div_mul_cancel₀ _ (ne_of_gt hμpos)]
    _ = Real.log ((1 + u) / μ) + Real.log μ := Real.log_mul (ne_of_gt h1) (ne_of_gt hμpos)
    _ ≤ ((1 + u) / μ - 1) + Real.log μ := by
          have h := Real.log_le_sub_one_of_pos h1; linarith
    _ ≤ Real.log μ + u / μ := by rw [h3]; linarith

/-- BW §13 (Yu's `L1.6` plus the `μ`-trick): for `k ≥ 1`, rational `x` and `μ ≥ 1`, `log|Θ(x;k,l,m)| ≤ kl·(1 + log μ + 1/μ) + l·|x|/μ`, where `Θ(x;k,l,m) = thetaRatQ x k l m = aeval x (hasseDeriv m (deltaPoly k ^ l))`. Derive from `est_Theta_yu` (`‖Theta z k l m‖ ≤ (e(1+‖z‖/k))^{kl}`) via the elementary inequality `log(1+t) ≤ log μ + t/μ` for `t = |x|/k ≥ 0`, `μ ≥ 1`. -/
theorem thetaRatQ_log_le (k : ℕ) (hk : 1 ≤ k) (l m : ℕ) (x : ℚ) (μ : ℝ) (hμ : 1 ≤ μ) :
    Real.log ‖((thetaRatQ x k l m : ℚ) : ℂ)‖ ≤
      (k * l : ℝ) * (1 + Real.log μ + 1 / μ) + (l : ℝ) * |(x : ℝ)| / μ := by
  rw [← thetaRatQ_cast x k l m]
  have hμpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  rcases eq_or_lt_of_le (norm_nonneg (Theta (x : ℂ) k l m)) with h0 | hpos
  · -- `Θ = 0`: the logarithm vanishes and the right-hand side is nonnegative.
    rw [← h0, Real.log_zero]
    have hlμ : 0 ≤ Real.log μ := Real.log_nonneg hμ
    have h1 : 0 ≤ (k : ℝ) * l * (1 + Real.log μ + 1 / μ) := by positivity
    have h2 : 0 ≤ (l : ℝ) * |(x : ℝ)| / μ := by positivity
    linarith
  · -- take logarithms in `est_Theta_yu`
    have hb := est_Theta_yu (x : ℂ) k l m hk
    have hlog := Real.log_le_log hpos hb
    rw [Real.log_pow, Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp] at hlog
    simp only [Nat.cast_mul] at hlog
    refine hlog.trans ?_
    have helem := log_one_add_le_log_mu_add (‖(x : ℂ)‖ / (k : ℝ)) μ (by positivity) hμ
    refine le_trans (mul_le_mul_of_nonneg_left (by linarith :
        1 + Real.log (1 + ‖(x : ℂ)‖ / (k : ℝ)) ≤
          1 + (Real.log μ + (‖(x : ℂ)‖ / (k : ℝ)) / μ)) (by positivity)) ?_
    have hkey : (k : ℝ) * l * ((‖(x : ℂ)‖ / (k : ℝ)) / μ) = (l : ℝ) * |(x : ℝ)| / μ := by
      have hkR : (k : ℝ) ≠ 0 := by positivity
      rw [Complex.norm_ratCast]
      field_simp
    calc (k : ℝ) * l * (1 + (Real.log μ + (‖(x : ℂ)‖ / (k : ℝ)) / μ))
        = (k : ℝ) * l * (1 + Real.log μ) + (l : ℝ) * |(x : ℝ)| / μ := by
          rw [mul_add, mul_add, hkey]; ring
      _ ≤ (k : ℝ) * l * (1 + Real.log μ) + (k : ℝ) * l / μ + (l : ℝ) * |(x : ℝ)| / μ := by
          have : (0 : ℝ) ≤ (k : ℝ) * l / μ := by positivity
          linarith
      _ = (k : ℝ) * l * (1 + Real.log μ + 1 / μ) + (l : ℝ) * |(x : ℝ)| / μ := by ring

end Work.BW

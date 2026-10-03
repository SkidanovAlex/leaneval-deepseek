import Mathlib

namespace Work.Pert.pert2v2

theorem dev_at_center_lt {A C T : ℝ} {Φ : ℂ → ℂ} {w : ℂ} (hA : 0 ≤ A)
    (hre : |w.re| < 1) (him : |w.im| = T)
    (hthr : A * Real.log (T + 3) + C + (T + 1) / 64 < T / 32)
    (hdev : ‖Φ w - w‖ ≤ A * Real.log (‖w‖ + 2) + C + ‖w‖ / 64) :
    ‖Φ w - w‖ < T / 32 := by
  -- `T = |w.im| ≥ 0`
  have hT : 0 ≤ T := by rw [← him]; exact abs_nonneg _
  -- `‖w‖² = w.re² + w.im²`
  have hnorm_sq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have him2 : w.im ^ 2 = T ^ 2 := by rw [← him, sq_abs]
  -- the real part is small: `w.re² < 1`
  have hre2 : w.re ^ 2 < 1 := by
    have hlt := abs_lt.mp hre
    nlinarith [hlt.1, hlt.2]
  -- hence `‖w‖ < T + 1`
  have hnorm_lt : ‖w‖ < T + 1 := by
    have h : ‖w‖ ^ 2 < (T + 1) ^ 2 := by
      rw [hnorm_sq, him2]; nlinarith
    have h2 := (sq_lt_sq.mp h)
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith)] at h2
    exact h2
  -- monotonicity of `log` and of division
  have hlog : Real.log (‖w‖ + 2) ≤ Real.log (T + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have h1 : A * Real.log (‖w‖ + 2) ≤ A * Real.log (T + 3) :=
    mul_le_mul_of_nonneg_left hlog hA
  have h2 : ‖w‖ / 64 ≤ (T + 1) / 64 := by linarith
  linarith

end Work.Pert.pert2v2

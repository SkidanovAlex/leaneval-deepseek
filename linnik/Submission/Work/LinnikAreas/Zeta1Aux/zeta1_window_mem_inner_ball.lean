import Mathlib

namespace Work.LinnikAreas.Zeta1Aux

/-- Any `u` with `0 < u.re < 1` and `|u.im - t| ≤ 3` lies in the closed ball of
radius `37/10` around `2 + I*t`: the squared distance is
`(u.re - 2)² + (u.im - t)² < 4 + 9 = 13 < (37/10)²`. -/
theorem zeta1_window_mem_inner_ball {t : ℝ} (ht : 5 ≤ |t|) {u : ℂ}
    (hre : 0 < u.re) (hre' : u.re < 1) (him : |u.im - t| ≤ 3) :
    u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10) := by
  rw [Metric.mem_closedBall, Complex.dist_eq]
  set w : ℂ := u - ((2 : ℂ) + Complex.I * (t : ℂ)) with hw
  have hwre : w.re = u.re - 2 := by simp [hw]
  have hwim : w.im = u.im - t := by simp [hw]
  have h1 : w.re ^ 2 < 4 := by
    rw [hwre]; nlinarith
  have h2 : w.im ^ 2 ≤ 9 := by
    rw [hwim]
    have := abs_le.mp him
    nlinarith [this.1, this.2]
  have hsq : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hlt : ‖w‖ ^ 2 < (37 / 10) ^ 2 := by
    rw [hsq]; nlinarith [h1, h2]
  have hfinal : ‖w‖ < 37 / 10 := by
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ < Real.sqrt ((37 / 10) ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) hlt
      _ = 37 / 10 := Real.sqrt_sq (by norm_num)
  exact le_of_lt hfinal

end Work.LinnikAreas.Zeta1Aux

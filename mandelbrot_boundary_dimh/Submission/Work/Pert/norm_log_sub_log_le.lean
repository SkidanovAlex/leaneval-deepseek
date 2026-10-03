import Mathlib

namespace Work.Pert

/-- Quantitative Lipschitz estimate for the principal branch of the complex logarithm:
if `L` lies in the open right half plane and `w` is within distance `r ≤ ‖L‖/2` of `L`,
then `‖log w - log L‖ ≤ (4/‖L‖) * ‖w - L‖`.

Indeed the closed ball of radius `r` around `L` avoids the branch cut `(-∞,0]`
(it is at distance `‖L‖` from `L`), so `log` is holomorphic there, and on that ball
`‖(log)' z‖ = 1/‖z‖ ≤ 2/‖L‖` because `‖z‖ ≥ ‖L‖ - r ≥ ‖L‖/2`. The mean value
inequality then gives the claim (even with constant `2`). -/
theorem norm_log_sub_log_le {L w : ℂ} {r : ℝ} (hLre : 0 < L.re) (hr : 0 < r)
    (hrL : r ≤ ‖L‖ / 2) (hw : ‖w - L‖ ≤ r) :
    ‖Complex.log w - Complex.log L‖ ≤ 4 / ‖L‖ * ‖w - L‖ := by
  have hLpos : 0 < ‖L‖ := lt_of_lt_of_le hLre (Complex.re_le_norm L)
  have hL2pos : 0 < ‖L‖ / 2 := by linarith
  have hLmem : L ∈ Metric.closedBall L r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_self, norm_zero]
    exact hr.le
  have hwmem : w ∈ Metric.closedBall L r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hw
  -- every point of the ball has norm at least `‖L‖/2`
  have hnorm_ge : ∀ z ∈ Metric.closedBall L r, ‖L‖ / 2 ≤ ‖z‖ := by
    intro z hz
    have hz' : ‖z - L‖ ≤ r := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp hz
    have h1 : ‖L‖ ≤ ‖L - z‖ + ‖z‖ := by
      have h := norm_add_le (L - z) z
      rwa [sub_add_cancel] at h
    rw [norm_sub_rev] at h1
    linarith
  -- the ball avoids the branch cut, so `log` is holomorphic on it
  have hslit : ∀ z ∈ Metric.closedBall L r, z ∈ Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff]
    by_cases h : 0 < z.re
    · exact Or.inl h
    · right
      intro him
      exfalso
      have hz' : ‖z - L‖ ≤ r := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hz
      have hnormsq : Complex.normSq L ≤ Complex.normSq (z - L) := by
        rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, him]
        have hzre : z.re ≤ 0 := not_lt.mp h
        nlinarith [hLre, hzre]
      have hle : ‖L‖ ≤ ‖z - L‖ := by
        have h2 : ‖L‖ ^ 2 ≤ ‖z - L‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.sq_norm]
          exact hnormsq
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h2
      linarith
  have hdiff : ∀ z ∈ Metric.closedBall L r, DifferentiableAt ℂ Complex.log z :=
    fun z hz => Complex.differentiableAt_log (hslit z hz)
  have hbound : ∀ z ∈ Metric.closedBall L r, ‖deriv Complex.log z‖ ≤ 2 / ‖L‖ := by
    intro z hz
    rw [Complex.deriv_log (hslit z hz), norm_inv]
    have hzge := hnorm_ge z hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hL2pos hzge
    have h : (2:ℝ) / ‖L‖ = (‖L‖ / 2)⁻¹ := by rw [inv_div]
    rw [h]
    exact (inv_le_inv₀ hzpos hL2pos).mpr hzge
  have hmain := (convex_closedBall L r).norm_image_sub_le_of_norm_deriv_le hdiff hbound hLmem hwmem
  refine hmain.trans ?_
  have h2 : (2:ℝ)/‖L‖ ≤ 4/‖L‖ := by
    rw [div_le_div_iff_of_pos_right hLpos]
    norm_num
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

end Work.Pert

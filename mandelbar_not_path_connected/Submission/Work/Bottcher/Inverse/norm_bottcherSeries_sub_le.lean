/-
# Lipschitz estimate for the Böttcher series on a small far ball

`bottcherSeries c z = Σ_n 4^{-(n+1)} log (normFactor c (p_c^n z))`, `p_c = T_c^2`,
is holomorphic on the far region `{4 (1 + ‖c‖) ≤ ‖z‖}`, with derivative
`O(1/‖z‖³)`: the sum of the termwise derivatives is dominated by
`64 (1 + ‖c‖)/‖z‖³` (`Work.Bottcher.Contraction.norm_tsum_btDeriv_le`).

Consequently, on the closed ball of radius `‖u‖ / 8` around a point `u` with
`128 (1 + ‖c‖) + 128 ≤ ‖u‖` -- whose points all satisfy `‖w‖ ≥ (7/8)‖u‖ ≥
4 (1 + ‖c‖)` -- the series is Lipschitz with the explicit constant
`128 (‖c‖² + 3‖c‖ + 1)/‖u‖³`:

`‖B_c x - B_c y‖ ≤ 128 (‖c‖² + 3‖c‖ + 1) / ‖u‖³ · ‖x - y‖`.

The constant comparison is `64 · (8/7)³ · (1 + ‖c‖) ≤ 128 (‖c‖² + 3‖c‖ + 1)`,
which holds for every `‖c‖ ≥ 0`.

This is the form in which the Lipschitz estimate is consumed by the construction
of the inverse Böttcher coordinate (a fixed-point contraction argument).
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Inverse.norm_bottcherSeries_le_far
import Submission.Work.Bottcher.Inverse.differentiableOn_bottcherSeries_ball
import Submission.Work.Bottcher.Contraction.norm_bottcherSeries_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Inverse

theorem norm_bottcherSeries_sub_le (c u : ℂ) (hu : 128 * (1 + ‖c‖) + 128 ≤ ‖u‖) {x y : ℂ}
    (hx : x ∈ Metric.closedBall u (‖u‖ / 8)) (hy : y ∈ Metric.closedBall u (‖u‖ / 8)) :
    ‖Work.Bottcher.bottcherSeries c x - Work.Bottcher.bottcherSeries c y‖
      ≤ 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 3 * ‖x - y‖ := by
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hu_pos : 0 < ‖u‖ := by linarith
  -- every point of the ball around `u` of radius `‖u‖ / 8` is far out
  have hfar : ∀ w ∈ Metric.closedBall u (‖u‖ / 8), 4 * (1 + ‖c‖) ≤ ‖w‖ := by
    intro w hw
    have hwge : (7 / 8 : ℝ) * ‖u‖ ≤ ‖w‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have h := norm_add_le w (u - w)
      have h2 : w + (u - w) = u := by ring
      rw [h2, norm_sub_rev u w] at h
      linarith
    have h7 : 4 * (1 + ‖c‖) ≤ (7 / 8 : ℝ) * ‖u‖ := by
      have hmul := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 7 / 8)
      nlinarith [hmul]
    linarith
  -- the series is complex differentiable on the ball, with derivative `Σ btDeriv`
  have hderiv : ∀ w ∈ Metric.closedBall u (‖u‖ / 8),
      HasFDerivWithinAt (Work.Bottcher.bottcherSeries c)
        (ContinuousLinearMap.toSpanSingleton ℂ
          (∑' n : ℕ, Work.Bottcher.Core.btDeriv c n w))
        (Metric.closedBall u (‖u‖ / 8)) w := fun w hw =>
    ((Work.Bottcher.Contraction.hasDerivAt_bottcherSeries c w (hfar w hw)).hasFDerivAt).hasFDerivWithinAt
  -- ... and its derivative is uniformly bounded by the claimed constant
  have hbound : ∀ w ∈ Metric.closedBall u (‖u‖ / 8),
      ‖ContinuousLinearMap.toSpanSingleton ℂ
          (∑' n : ℕ, Work.Bottcher.Core.btDeriv c n w)‖
        ≤ 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 3 := by
    intro w hw
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    have h1 := Work.Bottcher.Contraction.norm_tsum_btDeriv_le c w (hfar w hw)
    have hwge : (7 / 8 : ℝ) * ‖u‖ ≤ ‖w‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have h := norm_add_le w (u - w)
      have h2 : w + (u - w) = u := by ring
      rw [h2, norm_sub_rev u w] at h
      linarith
    have hW : 0 < ‖w‖ := by linarith
    have h2 : 64 * (1 + ‖c‖) / ‖w‖ ^ 3 ≤ 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hW 3) (pow_pos hu_pos 3)]
      have hU3 : ‖u‖ ^ 3 ≤ (8 / 7 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
        have h8 : ‖u‖ ≤ (8 / 7 : ℝ) * ‖w‖ := by linarith
        have hpow := pow_le_pow_left₀ (norm_nonneg u) h8 3
        rwa [mul_pow] at hpow
      have hconst : 64 * (1 + ‖c‖) * (8 / 7 : ℝ) ^ 3 ≤ 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) := by
        have h : (8 / 7 : ℝ) ^ 3 = 512 / 343 := by norm_num
        rw [h]; nlinarith [hc, sq_nonneg ‖c‖]
      calc 64 * (1 + ‖c‖) * ‖u‖ ^ 3
          ≤ 64 * (1 + ‖c‖) * ((8 / 7 : ℝ) ^ 3 * ‖w‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hU3 (by positivity)
        _ = (64 * (1 + ‖c‖) * (8 / 7 : ℝ) ^ 3) * ‖w‖ ^ 3 := by ring
        _ ≤ 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) * ‖w‖ ^ 3 :=
            mul_le_mul_of_nonneg_right hconst (by positivity)
    linarith
  -- mean value inequality on the convex closed ball
  have hMVT := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    (convex_closedBall u (‖u‖ / 8)) hx hy
  rw [norm_sub_rev (Work.Bottcher.bottcherSeries c y) (Work.Bottcher.bottcherSeries c x),
      norm_sub_rev y x] at hMVT
  exact hMVT

end Work.Bottcher.Inverse

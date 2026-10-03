/-
# `Submission.Work.FIArea6Hecke.R.oneSidedToTwoSided` — the Landau–Littlewood step

The abstract core of the reduction of `R/heckeStripLogDeriv` (the *norm* bound for `L'/L` in the
zero-free region) to the **one-sided** bound `Re (L'/L) ≥ -C·log` (`R/LogDerivStatementDefs`).

If `F` is analytic on `Metric.ball c R` and its *real part* is bounded above on the ball by `Bnd`,
and the value at the centre is bounded by `Bndc`, then Borel–Carathéodory applied to
`G = F - F c` (`Commons.Analysis/Complex/borelCaratheodory_deriv_le`) bounds `‖G'‖ ≤ 8(Bnd+Bndc)/R`
on the ball of half the radius, and the mean-value inequality along the segment `[c,s]` gives

  `‖F s‖ ≤ 5·(Bnd + Bndc)`   for `‖s - c‖ ≤ R/2`.

This is exactly the passage used in `Commons/NumberTheory/Zeta/zeta_inv_le_log_zeroFree`
(`hzeta_bound`): a one-sided bound plus the value at one point controls the full modulus.
-/
import Mathlib
import Submission.Commons.Analysis.Complex.borelCaratheodory_deriv_le

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Complex Metric

noncomputable section

/-- Mean-value inequality on a segment, from a bound on the derivative. -/
private theorem norm_sub_le_of_segment {F : ℂ → ℂ} {x y : ℂ} {K : ℝ}
    (hF : ∀ w ∈ segment ℝ x y, HasDerivAt F (deriv F w) w)
    (hK : ∀ w ∈ segment ℝ x y, ‖deriv F w‖ ≤ K) :
    ‖F y - F x‖ ≤ K * ‖y - x‖ := by
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F) (s := segment ℝ x y) (C := K)
    (f' := fun w => ContinuousLinearMap.toSpanSingleton ℂ (deriv F w))
    (x := x) (y := y) ?_ ?_ (convex_segment x y) (left_mem_segment ℝ x y)
    (right_mem_segment ℝ x y)
  · intro w hw
    exact ((hF w hw).hasFDerivAt).hasFDerivWithinAt
  · intro w hw
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    exact hK w hw

/-- **One-sided ⟹ two-sided (Landau–Littlewood).**  If `F` is analytic on `Metric.ball c R`, has
`Re F ≤ Bnd` there, and `‖F c‖ ≤ Bndc`, then `‖F s‖ ≤ 5 (Bnd + Bndc)` for every `s` with
`‖s - c‖ ≤ R/2`. -/
theorem norm_le_of_re_le_center {F : ℂ → ℂ} {c : ℂ} {R Bnd Bndc : ℝ}
    (hR : 0 < R) (hBnd : 0 ≤ Bnd) (hBndc : 0 ≤ Bndc)
    (hF : AnalyticOnNhd ℂ F (Metric.ball c R))
    (hre : ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re ≤ Bnd)
    (hc : ‖F c‖ ≤ Bndc) :
    ∀ s : ℂ, ‖s - c‖ ≤ R / 2 → ‖F s‖ ≤ 5 * (Bnd + Bndc) := by
  intro s hs
  set G : ℂ → ℂ := fun w => F w - F c with hG
  have hGan : AnalyticOnNhd ℂ G (Metric.ball c R) :=
    hF.sub (analyticOnNhd_const (v := F c) (s := Metric.ball c R))
  have hGc : G c = 0 := by simp [hG]
  have hreG : ∀ w : ℂ, w ∈ Metric.ball c R → (G w).re ≤ Bnd + Bndc := by
    intro w hw
    have h1 : (G w).re = (F w).re - (F c).re := by simp [hG, Complex.sub_re]
    have h2 : |(F c).re| ≤ ‖F c‖ := Complex.abs_re_le_norm _
    rw [h1]
    have h3 := (abs_le.mp h2).1
    linarith [hre w hw, h3, hc]
  have hB : 0 ≤ Bnd + Bndc := by linarith
  have hBC := Commons.Analysis.Complex.borelCaratheodory_deriv_le (F := G) (c := c) (R := R)
    (B := Bnd + Bndc) hR hB hGan hGc hreG
  have hderiv : ∀ z : ℂ, ‖z - c‖ ≤ R / 2 → ‖deriv G z‖ ≤ 8 * (Bnd + Bndc) / R := by
    intro z hz
    have hzm : z ∈ Metric.ball c R := by
      rw [Metric.mem_ball, dist_eq_norm]; linarith [hz, hR]
    have hb := hBC z hzm
    have hden : R / 2 ≤ R - ‖z - c‖ := by linarith
    have hdenpos : 0 < R - ‖z - c‖ := by linarith
    have hsq : R ^ 2 ≤ 4 * (R - ‖z - c‖) ^ 2 := by nlinarith [hden, hR]
    have hkey : 2 * R * (Bnd + Bndc) / (R - ‖z - c‖) ^ 2 ≤ 8 * (Bnd + Bndc) / R := by
      rw [div_le_div_iff₀ (pow_pos hdenpos 2) hR]
      nlinarith [hsq, hB]
    linarith [hb, hkey]
  have hseg : ∀ w ∈ segment ℝ c s, ‖w - c‖ ≤ R / 2 := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨θ, hθ, rfl⟩ := hw
    have hsub : (c + θ • (s - c)) - c = θ • (s - c) := by rw [add_sub_cancel_left]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    nlinarith [hθ.2, norm_nonneg (s - c), hs]
  have h1 : ∀ w ∈ segment ℝ c s, HasDerivAt G (deriv G w) w := by
    intro w hw
    have hw' : w ∈ Metric.ball c R := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hseg w hw, hR]
    exact (hGan.differentiableOn.differentiableAt
      (Metric.isOpen_ball.mem_nhds hw')).hasDerivAt
  have h2 : ∀ w ∈ segment ℝ c s, ‖deriv G w‖ ≤ 8 * (Bnd + Bndc) / R :=
    fun w hw => hderiv w (hseg w hw)
  have hmv := norm_sub_le_of_segment h1 h2
  have hGs : ‖G s‖ ≤ 8 * (Bnd + Bndc) / R * (R / 2) := by
    have h3 : ‖G s - G c‖ ≤ 8 * (Bnd + Bndc) / R * ‖s - c‖ := hmv
    rw [hGc, sub_zero] at h3
    refine h3.trans ?_
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have h4 : 8 * (Bnd + Bndc) / R * (R / 2) = 4 * (Bnd + Bndc) := by
    field_simp
    ring
  rw [h4] at hGs
  have h5 : ‖F s‖ ≤ ‖G s‖ + ‖F c‖ := by
    calc ‖F s‖ = ‖G s + F c‖ := by rw [hG]; ring_nf
    _ ≤ ‖G s‖ + ‖F c‖ := norm_add_le _ _
  linarith [h5, hGs, hc, hBnd, hBndc]

end

end Work.FIArea6Hecke.R

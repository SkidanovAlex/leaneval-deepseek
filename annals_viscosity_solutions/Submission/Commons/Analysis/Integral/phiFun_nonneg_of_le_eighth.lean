import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

open MeasureTheory intervalIntegral Real

namespace Commons.Analysis.Integral

/-- For `0 ≤ v ≤ 1/8`, the circle-average transfer integral is nonnegative.

The proof uses the elementary inequality `Real.log x ≤ x - 1` together with the
fact that the mean value over the unit circle of `log ‖z + v‖` vanishes
(Mathlib's `circleAverage_log_norm_sub_const₀`), which gives
`(1/(2π)) ∫_θ log ((1 + v² + 2 v cos θ)^{-1/2}) = 0`. -/
theorem phiFun_nonneg_of_le_eighth (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ 1 / 8) :
    0 ≤ (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1) := by
  have hv1 : v < 1 := by linarith
  -- The base `1 + v² + 2 v cos θ` is strictly positive.
  have hbase_pos : ∀ θ : ℝ, 0 < 1 + v ^ 2 + 2 * v * Real.cos θ := by
    intro θ
    nlinarith [sq_nonneg (1 - v), Real.neg_one_le_cos θ, hv0]
  -- The complex norm `‖e^{iθ} + v‖` equals `√(1 + v² + 2 v cos θ)`.
  have hnorm : ∀ θ : ℝ,
      ‖circleMap 0 1 θ + (v : ℂ)‖ = Real.sqrt (1 + v ^ 2 + 2 * v * Real.cos θ) := by
    intro θ
    rw [Complex.norm_def]
    congr 1
    rw [Complex.normSq_apply, circleMap, Complex.ofReal_one, one_mul, zero_add]
    rw [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  -- `‖v‖ < 1` as a complex number.
  have hnorm_v : ‖(v : ℂ)‖ < 1 := by
    rw [← Real.sqrt_sq (norm_nonneg (v : ℂ)), Complex.sq_norm, Complex.normSq_ofReal]
    rw [show v * v = v ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hv0]
    exact hv1
  -- The circle average of `log ‖z - (-v)‖` over the unit circle vanishes.
  have hcircle : circleAverage (fun z : ℂ => Real.log ‖z - (-(v : ℂ))‖) 0 1 = 0 := by
    apply circleAverage_log_norm_sub_const₀
    rwa [norm_neg]
  -- Hence the interval integral of `log ‖circleMap 0 1 θ + v‖` vanishes.
  have h0 : ∫ θ in (0)..(2 * Real.pi), Real.log ‖circleMap 0 1 θ + (v : ℂ)‖ = 0 := by
    have hc := hcircle
    rw [Real.circleAverage_def] at hc
    simp only [smul_eq_mul, sub_neg_eq_add] at hc
    exact (mul_eq_zero.mp hc).resolve_left (by positivity)
  -- Rewriting the integrand as `log (√(1 + v² + 2 v cos θ))`.
  have hlogs :
      ∫ θ in (0)..(2 * Real.pi), Real.log (Real.sqrt (1 + v ^ 2 + 2 * v * Real.cos θ)) = 0 := by
    have heq : (∫ θ in (0)..(2 * Real.pi),
          Real.log (Real.sqrt (1 + v ^ 2 + 2 * v * Real.cos θ)))
        = ∫ θ in (0)..(2 * Real.pi), Real.log ‖circleMap 0 1 θ + (v : ℂ)‖ := by
      apply intervalIntegral.integral_congr
      intro θ _
      show Real.log (Real.sqrt (1 + v ^ 2 + 2 * v * Real.cos θ))
        = Real.log ‖circleMap 0 1 θ + (v : ℂ)‖
      rw [hnorm θ]
    rw [heq, h0]
  -- `(1 + v² + 2 v cos θ)^{-1/2} = (√(1 + v² + 2 v cos θ))⁻¹`.
  have hge : ∀ θ : ℝ,
      (1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2)
        = (Real.sqrt (1 + v ^ 2 + 2 * v * Real.cos θ))⁻¹ := by
    intro θ
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by norm_num, Real.rpow_neg (hbase_pos θ).le,
      ← Real.sqrt_eq_rpow]
  -- The interval integral of `log ((1 + v² + 2 v cos θ)^{-1/2})` vanishes.
  have hlogg :
      ∫ θ in (0)..(2 * Real.pi),
          Real.log ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2)) = 0 := by
    have heq : (∫ θ in (0)..(2 * Real.pi),
            Real.log ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2)))
        = ∫ θ in (0)..(2 * Real.pi),
            -Real.log (Real.sqrt (1 + v ^ 2 + 2 * v * Real.cos θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      show Real.log ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2))
        = -Real.log (Real.sqrt (1 + v ^ 2 + 2 * v * Real.cos θ))
      rw [hge θ, Real.log_inv]
    rw [heq, intervalIntegral.integral_neg, hlogs, neg_zero]
  -- Continuity / integrability.
  have hcont_g : Continuous fun θ : ℝ =>
      (1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2) := by
    refine Continuous.rpow_const (by fun_prop) ?_
    intro θ; left; exact ne_of_gt (hbase_pos θ)
  have hcont_lg : Continuous fun θ : ℝ =>
      Real.log ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2)) :=
    hcont_g.log fun θ => ne_of_gt (Real.rpow_pos_of_pos (hbase_pos θ) _)
  -- Pointwise inequality `log x ≤ x - 1`.
  have hpt : ∀ θ : ℝ,
      Real.log ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2))
        ≤ (1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2) - 1 := by
    intro θ
    exact Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (hbase_pos θ) _)
  have hmono :
      (∫ θ in (0)..(2 * Real.pi),
          Real.log ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2)))
        ≤ ∫ θ in (0)..(2 * Real.pi),
            ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2) - 1) := by
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ ?_
    · exact hcont_lg.intervalIntegrable _ _
    · exact (hcont_g.sub continuous_const).intervalIntegrable _ _
    · intro θ _; exact hpt θ
  have hint : 0 ≤ ∫ θ in (0)..(2 * Real.pi),
      ((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1 : ℝ) / 2) - 1) :=
    le_trans (le_of_eq hlogg.symm) hmono
  exact mul_nonneg (by positivity) hint

end Commons.Analysis.Integral
import Mathlib
import Submission.Work.EQ.GermSetup
import Submission.Work.EQ.SqrtNearOne

namespace Work.EQ

open Complex Metric

/-- `GnlOf a ρ` is analytic wherever the ingredients are: the two shifts `u ↦ ρ (λ u)`,
`u ↦ ρ (u/λ)` and `u ↦ ρ u` are analytic on `ball 0 (λ · germR a)`, the square root
`SOf ρ` is analytic there because its argument stays in the slit plane (`‖u² β²‖ < 1` on the
ball, using the bound `‖ρ‖ ≤ 1`), and hence `WOf ρ` is analytic as a quotient with nonvanishing
denominator. The rest is arithmetic. -/
theorem Gnl_analytic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : AnalyticOnNhd ℂ ρ (Metric.ball 0 (germR a)))
    (hb : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) :
    AnalyticOnNhd ℂ (GnlOf a ρ) (Metric.ball 0 (eqLam a * germR a)) := by
  have hnorm_lam : ‖lamC a‖ = eqLam a := by
    simp only [lamC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eqLam_pos ha0 ha1)]
  have hb_sub : Metric.ball (0:ℂ) (eqLam a * germR a) ⊆ Metric.ball (0:ℂ) (germR a) := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right] at hu ⊢
    have hp := eqLam_pos ha0 ha1
    have hr := germR_pos ha0 ha1
    have hl := eqLam_lt_one ha0 ha1
    nlinarith
  have hρs : AnalyticOnNhd ℂ ρ (Metric.ball 0 (eqLam a * germR a)) := hρ.mono hb_sub
  have hρl : AnalyticOnNhd ℂ (fun u => ρ (lamC a * u))
      (Metric.ball 0 (eqLam a * germR a)) := by
    refine hρ.comp ?_ ?_
    · exact analyticOnNhd_const.mul analyticOnNhd_id
    · intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu ⊢
      rw [norm_mul, hnorm_lam]
      have hp := eqLam_pos ha0 ha1
      have hr := germR_pos ha0 ha1
      have hl := eqLam_lt_one ha0 ha1
      nlinarith [norm_nonneg u]
  have hρd : AnalyticOnNhd ℂ (fun u => ρ (u / lamC a))
      (Metric.ball 0 (eqLam a * germR a)) := by
    refine hρ.comp ?_ ?_
    · exact analyticOnNhd_id.div_const
    · intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu ⊢
      rw [norm_div, hnorm_lam]
      have hp := eqLam_pos ha0 ha1
      rw [div_lt_iff₀ hp]
      have hr := germR_pos ha0 ha1
      nlinarith [hu]
  have hbeta : AnalyticOnNhd ℂ (betaOf ρ) (Metric.ball 0 (eqLam a * germR a)) := by
    unfold betaOf
    exact analyticOnNhd_const.add ((analyticOnNhd_id.pow 2).mul hρs)
  have hgg_bound : ∀ u, u ∈ Metric.ball (0:ℂ) (eqLam a * germR a) →
      ‖u ^ 2 * (betaOf ρ u) ^ 2‖ < 1 := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right] at hu
    have h_half : ‖u‖ < 1/2 := by
      have hg : germR a ≤ 1/16 := by
        have h := germR_le_lam_sq a
        have hp := eqLam_pos ha0 ha1
        have hl := eqLam_lt_one ha0 ha1
        have hsq : (eqLam a)^2 ≤ 1 := by nlinarith
        have h2 : (eqLam a)^2 / 16 ≤ 1/16 := by linarith
        linarith
      have hle0 : eqLam a ≤ 1 := le_of_lt (eqLam_lt_one ha0 ha1)
      have hpos := germR_pos ha0 ha1
      have hle : eqLam a * germR a ≤ 1/16 := by
        have hh := mul_le_mul_of_nonneg_right hle0 (le_of_lt hpos)
        linarith
      linarith
    have hule : ‖u‖ ≤ germR a := by
      have hp := eqLam_pos ha0 ha1
      have hr := germR_pos ha0 ha1
      have hl : eqLam a ≤ 1 := le_of_lt (eqLam_lt_one ha0 ha1)
      have hh : eqLam a * germR a ≤ germR a := by nlinarith
      linarith
    have hρu : ‖ρ u‖ ≤ 1 := hb u hule
    have hbeta2 : ‖betaOf ρ u‖ ≤ 2 := by
      unfold betaOf
      have h1 : ‖(-1:ℂ) + u ^ 2 * ρ u‖ ≤ ‖(-1:ℂ)‖ + ‖u ^ 2 * ρ u‖ := norm_add_le _ _
      rw [norm_neg, norm_one, norm_mul, norm_pow] at h1
      have h2 : ‖u‖ ^ 2 * ‖ρ u‖ ≤ (1/2)^2 * 1 :=
        mul_le_mul (by nlinarith [norm_nonneg u]) hρu (norm_nonneg _) (by norm_num)
      linarith
    have hbetaSq : ‖betaOf ρ u‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (betaOf ρ u)]
    have hu2lt : ‖u‖ ^ 2 < 1/4 := by nlinarith [norm_nonneg u]
    rw [norm_mul, norm_pow, norm_pow]
    have h1 : ‖u‖ ^ 2 * ‖betaOf ρ u‖ ^ 2 ≤ ‖u‖ ^ 2 * 4 :=
      mul_le_mul_of_nonneg_left hbetaSq (by positivity)
    have h2 : ‖u‖ ^ 2 * 4 < 1 := by linarith
    linarith
  have hS : AnalyticOnNhd ℂ (SOf ρ) (Metric.ball 0 (eqLam a * germR a)) := by
    have hf : AnalyticOnNhd ℂ (fun u => 1 + u ^ 2 * (betaOf ρ u) ^ 2)
        (Metric.ball 0 (eqLam a * germR a)) :=
      analyticOnNhd_const.add ((analyticOnNhd_id.pow 2).mul (hbeta.pow 2))
    have hslit : ∀ u ∈ Metric.ball (0:ℂ) (eqLam a * germR a),
        (1 + u ^ 2 * (betaOf ρ u) ^ 2) ∈ Complex.slitPlane := by
      intro u hu
      rw [Complex.mem_slitPlane_iff]
      left
      have hlt := hgg_bound u hu
      have hre : (1 + u ^ 2 * (betaOf ρ u) ^ 2).re = 1 + (u ^ 2 * (betaOf ρ u) ^ 2).re := by
        rw [Complex.add_re, Complex.one_re]
      rw [hre]
      have hb2 : -(‖u ^ 2 * (betaOf ρ u) ^ 2‖) ≤ (u ^ 2 * (betaOf ρ u) ^ 2).re := by
        have h := Complex.abs_re_le_norm (u ^ 2 * (betaOf ρ u) ^ 2)
        linarith [(abs_le.mp h).1]
      linarith
    exact hf.cpow analyticOnNhd_const hslit
  have hW : AnalyticOnNhd ℂ (WOf ρ) (Metric.ball 0 (eqLam a * germR a)) := by
    unfold WOf
    refine (hbeta.pow 2).div (analyticOnNhd_const.add hS) ?_
    intro u hu
    have hlt := hgg_bound u hu
    have hs : SOf ρ u = sqHalf (u ^ 2 * (betaOf ρ u) ^ 2) := rfl
    rw [hs]
    intro h
    exact sqHalf_add_one_ne_zero hlt (by rwa [add_comm] at h)
  have hA1 : AnalyticOnNhd ℂ (A1Of a ρ) (Metric.ball 0 (eqLam a * germR a)) := by
    unfold A1Of
    exact hρs.sub (analyticOnNhd_const.mul hρd)
  have hA2 : AnalyticOnNhd ℂ (A2Of a ρ) (Metric.ball 0 (eqLam a * germR a)) := by
    unfold A2Of
    exact (analyticOnNhd_const.mul hρl).sub hρs
  have hA3 : AnalyticOnNhd ℂ (A3Of a ρ) (Metric.ball 0 (eqLam a * germR a)) := by
    unfold A3Of
    exact (analyticOnNhd_const.mul hρl).sub (analyticOnNhd_const.mul hρd)
  have h1 : AnalyticOnNhd ℂ (fun u => -((a : ℂ) * kapC a * WOf ρ u))
      (Metric.ball 0 (eqLam a * germR a)) :=
    ((analyticOnNhd_const (v := (a:ℂ) * kapC a)).mul hW).neg
  have h2 : AnalyticOnNhd ℂ (fun u => u ^ 2 * A1Of a ρ u * A2Of a ρ u)
      (Metric.ball 0 (eqLam a * germR a)) :=
    ((analyticOnNhd_id.pow 2).mul hA1).mul hA2
  have h3 : AnalyticOnNhd ℂ (fun u => (a : ℂ) * u ^ 2 * ρ u * A3Of a ρ u)
      (Metric.ball 0 (eqLam a * germR a)) :=
    (((analyticOnNhd_const (v := (a:ℂ))).mul (analyticOnNhd_id.pow 2)).mul hρs).mul hA3
  have h4 : AnalyticOnNhd ℂ
      (fun u => (a : ℂ) * u ^ 2 * WOf ρ u * (-(A3Of a ρ u) + kapC a * ρ u))
      (Metric.ball 0 (eqLam a * germR a)) :=
    ((((analyticOnNhd_const (v := (a:ℂ))).mul (analyticOnNhd_id.pow 2)).mul hW).mul
      (hA3.neg.add ((analyticOnNhd_const (v := kapC a)).mul hρs)))
  have h5 : AnalyticOnNhd ℂ (fun u => (a : ℂ) * u ^ 4 * WOf ρ u * ρ u * A3Of a ρ u)
      (Metric.ball 0 (eqLam a * germR a)) :=
    ((((analyticOnNhd_const (v := (a:ℂ))).mul (analyticOnNhd_id.pow 4)).mul hW).mul hρs).mul hA3
  have hsum : AnalyticOnNhd ℂ (fun u =>
      -((a : ℂ) * kapC a * WOf ρ u) + u ^ 2 * A1Of a ρ u * A2Of a ρ u
      + (a : ℂ) * u ^ 2 * ρ u * A3Of a ρ u
      + (a : ℂ) * u ^ 2 * WOf ρ u * (-(A3Of a ρ u) + kapC a * ρ u)
      + (a : ℂ) * u ^ 4 * WOf ρ u * ρ u * A3Of a ρ u)
      (Metric.ball 0 (eqLam a * germR a)) :=
    (((h1.add h2).add h3).add h4).add h5
  unfold GnlOf
  exact hsum

end Work.EQ

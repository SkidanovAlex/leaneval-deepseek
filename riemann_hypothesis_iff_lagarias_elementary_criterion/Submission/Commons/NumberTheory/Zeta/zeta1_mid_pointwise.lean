import Mathlib
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound
import Submission.Commons.NumberTheory.Zeta.zeta1_re_two_lower
import Submission.Commons.NumberTheory.Zeta.zeta1_growth_disk4

open Complex Filter Metric Set
open scoped Topology Real BigOperators
noncomputable section
set_option maxHeartbeats 0

namespace Commons.NumberTheory.Zeta

theorem zeta1_mid_pointwise (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ T Tp δ : ℝ, 5 ≤ T → T ≤ Tp → Tp ≤ T + 1 → 0 < δ → δ ≤ 1 / 4 →
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (Tp : ℂ))‖ < (3 / 2 : ℝ) + δ ^ 2 / 4 →
        riemannZeta₁ w ≠ 0) →
      ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ (5 / 8 : ℝ) →
        ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) / (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := by
  rcases zeta1_growth_disk4 with ⟨K, hK0, hKgrow⟩
  set C1 : ℝ := Real.log (max K 1) with hC1def
  have hC1 : 0 ≤ C1 := by
    rw [hC1def]; exact Real.log_nonneg (le_max_right K 1)
  refine ⟨100 * (C1 + 31), by positivity, ?_⟩
  intro T Tp δ hT hTTp hTp1 hδ0 hδ4 hfree σ hσlo hσhi
  -- basic facts about the parameters
  have hTp5 : 5 ≤ Tp := le_trans hT hTTp
  have hTp_pos : 0 < Tp := by linarith
  have hδ2pos : 0 < δ ^ 2 := by positivity
  have hδ4pos : 0 < δ ^ 2 / 4 := by positivity
  -- definitions
  set c : ℂ := (2 : ℂ) + Complex.I * (Tp : ℂ) with hc
  set R : ℝ := 3 / 2 + δ ^ 2 / 4 with hRdef
  set M : ℝ := K * (|Tp| + 7) ^ 15 with hMdef
  set A : ℝ := Real.log (2 * M) - Real.log (1 / 4) with hAdef
  set z₀ : ℂ := (σ : ℂ) + Complex.I * (Tp : ℂ) with hz0
  set ρ : ℝ := (σ - 1 / 2 + δ ^ 2 / 4) / 2 with hρdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  -- geometry
  have hnorm_zc : ‖z₀ - c‖ = |σ - 2| := by
    have hsub : z₀ - c = ((σ - 2 : ℝ) : ℂ) := by
      rw [hz0, hc]; apply Complex.ext <;> simp
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
  have hσ2 : σ - 2 ≤ 0 := by linarith
  have hd_eq : ‖z₀ - c‖ = 2 - σ := by
    rw [hnorm_zc, abs_of_nonpos hσ2]; ring
  have hz0_ball : z₀ ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm, hd_eq, hRdef]
    linarith [hσlo, hδ4pos]
  have hden_pos : 0 < σ - 1 / 2 + δ ^ 2 / 4 := by linarith [hσlo, hδ4pos]
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hRd : R - ‖z₀ - c‖ = σ - 1 / 2 + δ ^ 2 / 4 := by
    rw [hRdef, hd_eq]; ring
  have hρlt : ρ < R - ‖z₀ - c‖ := by
    rw [hRd, hρdef]; linarith
  -- zero-freeness on the ball
  have hg : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hgne : ∀ w : ℂ, w ∈ Metric.ball c R → riemannZeta₁ w ≠ 0 := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    exact hfree w (by rw [hRdef] at hw; simpa [hc] using hw)
  -- lower bound at the centre
  have hgm : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ c‖ := by
    simpa [hc] using zeta1_re_two_lower Tp
  -- growth bound on the ball
  have hTp_abs : 5 ≤ |Tp| := by rw [abs_of_pos hTp_pos]; exact hTp5
  have hgM : ∀ w : ℂ, w ∈ Metric.ball c R → ‖riemannZeta₁ w‖ ≤ M := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw4 : ‖w - c‖ ≤ 4 := by
      rw [hRdef] at hw
      nlinarith [hw, hδ4pos, hδ4]
    have hb := hKgrow Tp hTp_abs w (by simpa [hc] using hw4)
    rw [hMdef]
    exact hb
  have hMm : (1 / 4 : ℝ) ≤ M := le_trans hgm (hgM c (mem_ball_self hRpos))
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hMm
  -- the core ball bound
  have hbound :=
    Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound hg (c := c) (R := R)
      (m := 1 / 4) (M := M) hRpos (by norm_num) hMm hgne hgM hgm
      (z₀ := z₀) hz0_ball (ρ := ρ) hρ0 hρlt
  -- simplify the numerical factor
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have h : Real.log (1 / 4) ≤ Real.log (2 * M) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hnum_le : ‖z₀ - c‖ + ρ ≤ 2 := by
    rw [hd_eq, hρdef]
    have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
    nlinarith [hσlo]
  have hdenom : (R - ‖z₀ - c‖ - ρ) * ρ = (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 / 4 := by
    rw [hRd, hρdef]; ring
  have hb2 : ‖deriv riemannZeta₁ z₀ / riemannZeta₁ z₀‖ ≤
      16 * A / (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := by
    rw [hdenom] at hbound
    have h2A : 0 ≤ 2 * A := by linarith
    have hnum : 2 * A * (‖z₀ - c‖ + ρ) ≤ 2 * A * 2 :=
      mul_le_mul_of_nonneg_left hnum_le h2A
    have h1 : 2 * A * (‖z₀ - c‖ + ρ) / ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2 / 4) ≤
        2 * A * 2 / ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2 / 4) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have h3 : 2 * A * 2 / ((σ - 1 / 2 + δ ^ 2 / 4) ^ 2 / 4) =
        16 * A / (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := by
      have hne : (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hden_pos)
      field_simp
      ring
    rw [h3] at h1
    linarith [hbound, h1]
  -- bound A by (C1 + 31) (log(T+3) + 1)
  have hA_le : A ≤ (C1 + 31) * (Real.log (T + 3) + 1) := by
    have hlogM : Real.log M = Real.log K + 15 * Real.log (|Tp| + 7) := by
      rw [hMdef, Real.log_mul (ne_of_gt hK0) (by positivity), Real.log_pow]
      ring
    have hlogK : Real.log K ≤ C1 := by
      rw [hC1def]; exact Real.log_le_log hK0 (le_max_left K 1)
    have hlogTp : Real.log (|Tp| + 7) ≤ Real.log 2 + Real.log (T + 3) := by
      rw [abs_of_pos hTp_pos]
      have h1 : Tp + 7 ≤ 2 * (T + 3) := by linarith
      calc Real.log (Tp + 7) ≤ Real.log (2 * (T + 3)) :=
            Real.log_le_log (by linarith) h1
        _ = Real.log 2 + Real.log (T + 3) :=
            Real.log_mul (by norm_num) (by linarith)
    have hlog8 : Real.log 8 ≤ Real.log (T + 3) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog2 : Real.log 2 ≤ Real.log (T + 3) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlogT3pos : 0 ≤ Real.log (T + 3) := le_trans (le_of_lt (Real.log_pos (by norm_num))) hlog2
    have hAeq : A = Real.log 8 + Real.log M := by
      rw [hAdef]
      have h1 : Real.log (2 * M) - Real.log (1 / 4) = Real.log (8 * M) := by
        rw [← Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < 2 * M)) (by norm_num : (1 / 4 : ℝ) ≠ 0)]
        congr 1
        ring
      rw [h1, Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hMpos)]
    rw [hAeq, hlogM]
    nlinarith [hlogK, hlogTp, hlog8, hlog2, hlogT3pos, hC1]
  -- final assembly
  have hDpos : 0 < (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := pow_pos hden_pos 2
  calc
    ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
        = ‖deriv riemannZeta₁ z₀ / riemannZeta₁ z₀‖ := by
          simp only [logDeriv_apply, hz0]
    _ ≤ 16 * A / (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := hb2
    _ ≤ 16 * ((C1 + 31) * (Real.log (T + 3) + 1)) / (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hDpos)
          nlinarith [hA_le]
    _ ≤ 100 * (C1 + 31) * (Real.log (T + 3) + 1) / (σ - 1 / 2 + δ ^ 2 / 4) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hDpos)
          nlinarith [hC1]

end Commons.NumberTheory.Zeta

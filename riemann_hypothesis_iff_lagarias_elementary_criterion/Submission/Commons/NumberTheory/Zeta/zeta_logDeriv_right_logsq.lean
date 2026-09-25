import Mathlib
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound
import Submission.Commons.NumberTheory.Zeta.zeta1_growth_disk4
import Submission.Commons.NumberTheory.Zeta.zeta1_re_two_lower
import Submission.Commons.NumberTheory.Zeta.zeta_ne_zero_of_rh_gt_half
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_strip_bound_rh

namespace Commons.NumberTheory.Zeta

open Complex Metric
open scoped Real Topology

/-- Assuming the Riemann hypothesis, `ζ'/ζ` is `O((log |t|)^2)` uniformly in the strip
`5/8 ≤ Re s ≤ 2`, `|Im s| ≥ 5`. -/
theorem zeta_logDeriv_right_logsq (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, (5 / 8 : ℝ) ≤ σ → σ ≤ 2 → 5 ≤ |t| →
      ‖deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (Real.log (|t| + 3)) ^ 2 := by
  rcases zeta1_growth_disk4 with ⟨Cg, hCg0, hCg⟩
  let K1 : ℝ := Real.log (8 * (Cg + 1)) + 15 * Real.log (3 / 2)
  have hK1pos : 0 < K1 := by
    have h1 : 0 < Real.log (8 * (Cg + 1)) := Real.log_pos (by linarith)
    have h2 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    dsimp [K1]; linarith
  refine ⟨25600 * K1 + 384000 + 1 / 5, by linarith, ?_⟩
  intro σ t hσlo hσhi ht
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  let R : ℝ := 7 / 5
  let M : ℝ := Cg * (|t| + 7) ^ 15 + 1
  let A : ℝ := Real.log (2 * M) - Real.log (1 / 4)
  let ρ : ℝ := (σ - 3 / 5) / 2
  have hRpos : 0 < R := by dsimp [R]; norm_num
  have hs_c : s - c = ((σ - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [s, c]
  have hdnorm : ‖s - c‖ = |σ - 2| := by
    rw [hs_c, Complex.norm_real, Real.norm_eq_abs]
  have hd_eq : ‖s - c‖ = 2 - σ := by
    rw [hdnorm, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    ring
  have hdR : ‖s - c‖ < R := by
    rw [hd_eq]; dsimp [R]; linarith
  have hs_ball : s ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hdR
  have hg : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hgne : ∀ w : ℂ, w ∈ Metric.ball c R → riemannZeta₁ w ≠ 0 := by
    intro w hw
    have hw1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwre : (1 / 2 : ℝ) < w.re := by
      have hre : |(w - c).re| ≤ ‖w - c‖ := Complex.abs_re_le_norm (w - c)
      have hre' : |w.re - 2| ≤ ‖w - c‖ := by simpa [c] using hre
      have hlow : -(w.re - 2) ≤ |w.re - 2| := neg_le_abs _
      dsimp [R] at hw1
      linarith
    exact zeta1_ne_zero_of_rh_gt_half h hwre
  have hgM : ∀ w : ℂ, w ∈ Metric.ball c R → ‖riemannZeta₁ w‖ ≤ M := by
    intro w hw
    have hw1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw4 : ‖w - c‖ ≤ 4 := by dsimp [R] at hw1; linarith
    have hb := hCg t ht w hw4
    dsimp [M]
    linarith
  have hgm : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ c‖ := by
    dsimp [c]; exact zeta1_re_two_lower t
  have hMm : (1 / 4 : ℝ) ≤ M := by
    dsimp [M]
    have h1 : (0 : ℝ) ≤ Cg * (|t| + 7) ^ 15 :=
      mul_nonneg hCg0.le (pow_nonneg (by positivity) 15)
    linarith
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R - ‖s - c‖ := by
    rw [hd_eq]; dsimp [R, ρ]; linarith
  have hcore := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound
    (g := riemannZeta₁) hg (c := c) (R := R) (m := (1 / 4)) (M := M)
    hRpos (by norm_num) hMm hgne hgM hgm (z₀ := s) hs_ball (ρ := ρ) hρ0 hρR
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hle : (1 / 4 : ℝ) ≤ 2 * M := by linarith [hMm]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hle
    linarith
  have hgeom : 2 * A * (‖s - c‖ + ρ) / ((R - ‖s - c‖ - ρ) * ρ) ≤ 25600 * A := by
    have hnum : ‖s - c‖ + ρ ≤ 2 := by rw [hd_eq]; dsimp [ρ]; linarith
    have hρge : (1 / 80 : ℝ) ≤ ρ := by dsimp [ρ]; linarith
    have hRsub : (1 / 80 : ℝ) ≤ R - ‖s - c‖ - ρ := by rw [hd_eq]; dsimp [R, ρ]; linarith
    have hden : (1 / 6400 : ℝ) ≤ (R - ‖s - c‖ - ρ) * ρ := by nlinarith [hRsub, hρge]
    have hdenpos : 0 < (R - ‖s - c‖ - ρ) * ρ :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 6400) hden
    rw [div_le_iff₀ hdenpos]
    have hA2 : (0 : ℝ) ≤ 2 * A := by linarith
    have h1 : 2 * A * (‖s - c‖ + ρ) ≤ 4 * A := by
      have := mul_le_mul_of_nonneg_left hnum hA2
      linarith [this]
    have h2 : 4 * A ≤ 25600 * A * ((R - ‖s - c‖ - ρ) * ρ) := by
      have hthis := mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ 25600 * A by linarith)
      have heq : 25600 * A * (1 / 6400) = 4 * A := by ring
      rw [← heq]
      exact hthis
    linarith [h1, h2]
  have hcore' : ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤ 25600 * A := by
    refine le_trans hcore ?_
    simpa only [A] using hgeom
  have hA_le1 : A ≤ Real.log (8 * (Cg + 1) * (|t| + 7) ^ 15) := by
    have hAeq : A = Real.log (8 * M) := by
      dsimp [A]
      rw [← Real.log_div (by linarith [hMm] : (2 * M) ≠ 0) (by norm_num : (1 / 4 : ℝ) ≠ 0)]
      congr 1
      ring
    rw [hAeq]
    apply Real.log_le_log
    · have h1 : (0 : ℝ) ≤ Cg * (|t| + 7) ^ 15 :=
        mul_nonneg hCg0.le (pow_nonneg (by positivity) 15)
      have h2 : (0 : ℝ) < M := by dsimp [M]; linarith
      linarith
    · dsimp [M]
      have hbase : (1 : ℝ) ≤ (|t| + 7) ^ 15 :=
        one_le_pow₀ (by linarith [abs_nonneg t])
      nlinarith [hbase]
  have hA_le2 : Real.log (8 * (Cg + 1) * (|t| + 7) ^ 15) ≤ K1 + 15 * Real.log (|t| + 3) := by
    have h1 : Real.log (8 * (Cg + 1) * (|t| + 7) ^ 15) =
        Real.log (8 * (Cg + 1)) + 15 * Real.log (|t| + 7) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    rw [h1]
    have hlog : Real.log (|t| + 7) ≤ Real.log (3 / 2) + Real.log (|t| + 3) := by
      have hle : |t| + 7 ≤ (3 / 2) * (|t| + 3) := by nlinarith [abs_nonneg t, ht]
      have h0 : (0 : ℝ) < |t| + 7 := by linarith [abs_nonneg t]
      have h := Real.log_le_log h0 hle
      rwa [Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) (by positivity : (|t| + 3 : ℝ) ≠ 0)] at h
    have hstep : Real.log (8 * (Cg + 1)) + 15 * Real.log (|t| + 7) ≤
        Real.log (8 * (Cg + 1)) + 15 * (Real.log (3 / 2) + Real.log (|t| + 3)) := by
      have h15 : (0 : ℝ) ≤ 15 := by norm_num
      have hh := mul_le_mul_of_nonneg_left hlog h15
      linarith [hh]
    calc Real.log (8 * (Cg + 1)) + 15 * Real.log (|t| + 7)
        ≤ Real.log (8 * (Cg + 1)) + 15 * (Real.log (3 / 2) + Real.log (|t| + 3)) := hstep
      _ = K1 + 15 * Real.log (|t| + 3) := by dsimp [K1]; ring
  have hA_le : A ≤ K1 + 15 * Real.log (|t| + 3) := le_trans hA_le1 hA_le2
  have hz1bd : ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤
      25600 * (K1 + 15 * Real.log (|t| + 3)) := by
    calc ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤ 25600 * A := hcore'
      _ ≤ 25600 * (K1 + 15 * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hA_le (by norm_num)
  have hsm1 : (5 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have him : (s - 1).im = t := by simp [s]
    rw [him] at h
    linarith
  have hsne1 : s ≠ 1 := by
    intro h1
    have h0 : ‖s - 1‖ = 0 := by rw [h1]; simp
    linarith
  have hz1s : riemannZeta₁ s ≠ 0 := hgne s hs_ball
  have hlogd := zeta_logDeriv_norm_le s hsne1 hz1s
  have hinv : 1 / ‖s - 1‖ ≤ (1 / 5 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) hsm1
  have hstep : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      25600 * (K1 + 15 * Real.log (|t| + 3)) + 1 / 5 := by
    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 1 / ‖s - 1‖ := hlogd
      _ ≤ 25600 * (K1 + 15 * Real.log (|t| + 3)) + 1 / 5 := by linarith [hz1bd, hinv]
  have hL1 : (1 : ℝ) ≤ Real.log (|t| + 3) := by
    have h2 : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have hlog8 : (2 : ℝ) ≤ Real.log 8 := by rw [h8]; linarith
    have hL : Real.log 8 ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 8) (by linarith [abs_nonneg t])
    linarith
  have hLsq1 : (1 : ℝ) ≤ (Real.log (|t| + 3)) ^ 2 := one_le_pow₀ hL1
  have hfin : 25600 * (K1 + 15 * Real.log (|t| + 3)) + 1 / 5 ≤
      (25600 * K1 + 384000 + 1 / 5) * (Real.log (|t| + 3)) ^ 2 := by
    have h1 : 25600 * K1 ≤ 25600 * K1 * (Real.log (|t| + 3)) ^ 2 := by
      have hnn : (0 : ℝ) ≤ 25600 * K1 := by linarith [hK1pos]
      calc 25600 * K1 = 25600 * K1 * 1 := by ring
        _ ≤ 25600 * K1 * (Real.log (|t| + 3)) ^ 2 := mul_le_mul_of_nonneg_left hLsq1 hnn
    have h2 : 384000 * Real.log (|t| + 3) ≤
        384000 * (Real.log (|t| + 3)) ^ 2 := by
      have hLL : Real.log (|t| + 3) ≤ (Real.log (|t| + 3)) ^ 2 := by nlinarith [hL1]
      exact mul_le_mul_of_nonneg_left hLL (by norm_num)
    have h3 : (1 / 5 : ℝ) ≤ 1 / 5 * (Real.log (|t| + 3)) ^ 2 := by nlinarith [hLsq1]
    linarith [h1, h2, h3]
  exact le_trans hstep hfin

end Commons.NumberTheory.Zeta

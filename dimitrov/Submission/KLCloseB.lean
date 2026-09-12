import Mathlib
import Submission.Core.FaAnalytic
import Submission.Core.F1Norm
import Submission.Core.FaPolar
import Submission.Core.FaConcave
import Submission.Core.D3
import Submission.Core.FaArcs
import Submission.Core.F5Bis
import Submission.Core.LogMean
import Submission.KLCloseA

noncomputable section

open scoped Real Complex
open Complex
open MeasureTheory
open Interval

namespace Submission.KLMain

open Submission.Core
open Submission.CoreB

/-- `weightAngle` is nonnegative. -/
lemma weightAngle_nonneg (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    (_hp : ∀ j : Fin n, 0 ≤ p j) (σ : ℝ) : 0 ≤ weightAngle n θ p σ := by
  unfold weightAngle
  exact Finset.prod_nonneg (by
    intro j hj
    exact Real.rpow_nonneg (norm_nonneg _) (p j))

/-- Existence of the parameter `a` with margin: for `0 ≤ M < 2` there is
`1 < a < 2` with `a * M < 2`. -/
lemma exists_margin_a {M : ℝ} (hM0 : 0 ≤ M) (hM2 : M < 2) :
    ∃ a : ℝ, 1 < a ∧ a < 2 ∧ a * M < 2 := by
  by_cases hM0c : M = 0
  · refine ⟨3 / 2, by norm_num, by norm_num, ?_⟩
    rw [hM0c]
    norm_num
  · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM0c)
    let b : ℝ := min 2 (2 / M)
    have hb1 : 1 < b := by
      dsimp [b]
      rw [lt_min_iff]
      constructor
      · norm_num
      · exact (one_lt_div hMpos).2 hM2
    have hb2 : b ≤ 2 := by
      dsimp [b]
      exact min_le_left 2 (2 / M)
    have hbM : b ≤ 2 / M := by
      dsimp [b]
      exact min_le_right 2 (2 / M)
    let a : ℝ := (1 + b) / 2
    have ha1 : 1 < a := by
      dsimp [a]
      linarith
    have ha2 : a < 2 := by
      dsimp [a]
      linarith
    have haM : a * M < 2 := by
      have ha_lt_b : a < b := by
        dsimp [a]
        linarith
      have ha_lt_d : a < 2 / M := lt_of_lt_of_le ha_lt_b hbM
      have hmul : a * M < (2 / M) * M := mul_lt_mul_of_pos_right ha_lt_d hMpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hMpos)] at hmul
    exact ⟨a, ha1, ha2, haM⟩

/-- The circle exponential equals the `circleMap` with center `0`, radius `1`. -/
lemma circleMap_zero_one_eq_E (σ : ℝ) : circleMap (0 : ℂ) 1 σ = E σ := by
  dsimp [circleMap, E]
  simp

/-- On the unit circle, `fa` at `circleMap 0 1 σ` equals `faE`. -/
lemma fa_circleMap_eq_faE (n : ℕ) (a : ℝ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) :
    fa n a (fun j : Fin n => E (θ j)) p (circleMap (0 : ℂ) 1 σ) = faE n a θ p σ := by
  rw [circleMap_zero_one_eq_E]
  rfl

/-- **Per-`a` absurdity (KL design D1–D5/R5).**  With `M` a global upper
bound of `weightAngle`, any `a ∈ (1,2)` with `a·M < 2` gives a
contradiction (via the nonnegativity of the circle mean of
`log‖2 − f_a‖` and the R5 zero-free-log step at `h(0) = 2 − a ∈ (0,1)`). -/
lemma per_a_absurd (n : ℕ) (hn : 0 < n) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : ∀ j : Fin n, 0 ≤ p j) (hsum : (∑ j : Fin n, p j) = (n : ℝ))
    (M : ℝ) (hMle : ∀ σ : ℝ, weightAngle n θ p σ ≤ M) {a : ℝ}
    (ha1 : 1 < a) (ha2 : a < 2) (ham : a * M < 2) : False := by
  let c : ℝ := a * M
  have hc : c < 2 := ham
  have ha0 : 0 ≤ a := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) ha1)
  have hmarg : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c := by
    intro σ
    dsimp [c]
    exact faE_margin n a M ha0 θ p hp hMle σ
  have hmean : 0 ≤ ∫ σ in 0..2 * Real.pi, Real.log ‖(2 : ℂ) - faE n a θ p σ‖ :=
    circle_mean_nonneg n hn a ha0 θ p hp hsum (c := c) hc hmarg
  have hd : DifferentiableOn ℂ
      (fun z : ℂ => (2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z)
      (Metric.ball (0 : ℂ) 1) := by
    refine (differentiableOn_const (2 : ℂ)).sub ?_
    exact fa_differentiableOn n a (fun j : Fin n => E (θ j)) p (by
      intro j; exact (norm_E (θ j)).le)
  have hh : AnalyticOn ℂ
      (fun z : ℂ => (2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z)
      (Metric.ball (0 : ℂ) 1) := hd.analyticOn Metric.isOpen_ball
  have hcont : ContinuousOn
      (fun z : ℂ => (2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z)
      (Metric.closedBall (0 : ℂ) 1) := by
    refine (continuousOn_const.sub ?_)
    exact fa_cont_closedBall n a ha0 θ p hp
  have hlow : ∀ z : ℂ, ‖z‖ ≤ 1 →
      2 - c ≤ ‖(2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z‖ :=
    two_sub_fa_lower_bound_closedBall n a ha0 θ p hp hc hmarg
  have hmpos : 0 < 2 - c := by linarith
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      m ≤ ‖(2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z‖ := by
    refine ⟨2 - c, hmpos, ?_⟩
    intro z hz
    exact hlow z (by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hz))
  have hmeanAvg : 0 ≤ Real.circleAverage
      (fun z : ℂ => Real.log ‖(2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z‖)
      (0 : ℂ) 1 := by
    rw [Real.circleAverage_def, smul_eq_mul]
    refine mul_nonneg (inv_nonneg.mpr (le_of_lt Real.two_pi_pos)) ?_
    have hint : (∫ σ in 0..2 * Real.pi,
        (fun z : ℂ => Real.log ‖(2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z‖)
          (circleMap (0 : ℂ) 1 σ))
        = ∫ σ in 0..2 * Real.pi, Real.log ‖(2 : ℂ) - faE n a θ p σ‖ := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      change Real.log ‖(2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p (circleMap (0 : ℂ) 1 σ)‖ =
        Real.log ‖(2 : ℂ) - faE n a θ p σ‖
      exact congrArg (fun x : ℂ => Real.log ‖(2 : ℂ) - x‖)
        (fa_circleMap_eq_faE n a θ p σ)
    rw [hint]
    exact hmean
  have hfa0 : fa n a (fun j : Fin n => E (θ j)) p 0 = (a : ℂ) := by
    unfold fa cPow
    simp
  have h0 : (2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p 0 = (2 : ℂ) - (a : ℂ) := by
    rw [hfa0]
  have hnorm0 : ‖(2 : ℂ) - (a : ℂ)‖ = 2 - a := by
    have hle : 0 ≤ 2 - a := by linarith
    have htwo : (2 : ℂ) = (((2 : ℝ) : ℂ)) := by norm_num
    rw [htwo]
    rw [← Complex.ofReal_sub]
    rw [Complex.norm_real]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg hle]
  have hltLog : Real.log ‖(2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p 0‖ < 0 := by
    rw [h0, hnorm0]
    exact (Real.log_neg_iff (by linarith)).2 (by linarith)
  exact boundary_log_nonneg_of_inner_log_neg
    (fun z : ℂ => (2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z)
    hh hcont hm hmeanAvg hltLog

/-- **Konyagin–Lev, angle form.**  For `n ≥ 1` points `E(θ_j)` on the unit
circle with weights `p_j ≥ 0` summing to `n`, some point `E σ` of the
circle satisfies `2 ≤ ∏_j ‖E σ − E(θ_j)‖^{p_j}`. -/
theorem koniagin_lev_angles (n : ℕ) (hn : 0 < n) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : ∀ j : Fin n, 0 ≤ p j) (hsum : (∑ j : Fin n, p j) = (n : ℝ)) :
    ∃ σ : ℝ, 2 ≤ weightAngle n θ p σ := by
  classical
  by_contra h
  have hlt : ∀ σ : ℝ, weightAngle n θ p σ < 2 := by
    intro σ
    by_contra hge
    exact h ⟨σ, le_of_not_gt hge⟩
  obtain ⟨σmax, hσle⟩ := weightAngle_max n θ p hp
  let M : ℝ := weightAngle n θ p σmax
  have hM0 : 0 ≤ M := weightAngle_nonneg n θ p hp σmax
  have hM2 : M < 2 := hlt σmax
  rcases exists_margin_a hM0 hM2 with ⟨a, ha1, ha2, ham⟩
  exact per_a_absurd n hn θ p hp hsum M hσle ha1 ha2 ham

/-- **Konyagin–Lev.**  For `n ≥ 1` points `z_j` on the unit circle with
weights `p_j ≥ 0` summing to `n`, some point `w` of the unit circle
satisfies `2 ≤ ∏_j ‖w − z_j‖^{p_j}`. -/
theorem koniagin_lev_circle (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ) (p : Fin n → ℝ)
    (hz : ∀ j : Fin n, ‖z j‖ = 1) (hp : ∀ j : Fin n, 0 ≤ p j)
    (hsum : (∑ j : Fin n, p j) = (n : ℝ)) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ 2 ≤ ∏ j : Fin n, ‖w - z j‖ ^ p j := by
  classical
  let θ : Fin n → ℝ := fun j => Classical.choose (exists_E_eq_of_norm_one (hz j))
  have hθ : ∀ j : Fin n, E (θ j) = z j := by
    intro j
    dsimp [θ]
    exact Classical.choose_spec (exists_E_eq_of_norm_one (hz j))
  rcases koniagin_lev_angles n hn θ p hp hsum with ⟨σ, hσ⟩
  refine ⟨E σ, norm_E σ, ?_⟩
  have hprod : weightAngle n θ p σ = ∏ j : Fin n, ‖E σ - z j‖ ^ p j := by
    unfold weightAngle
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    rw [hθ j]
  simpa [hprod] using hσ

end Submission.KLMain

end

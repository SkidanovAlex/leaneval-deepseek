/-
# The pointwise slope estimate `(point)` for limits of classical solutions

`Submission.AlexandrovSlope.point_estimate` derives the pointwise estimate `(point)` of
Shankar--Yuan, §3 for a viscosity solution `g`, using Trudinger--Wang's weighted interior gradient
estimate (`GradientEstimateInput`) applied to `g` itself.

Here we derive the same estimate for `g` when `g` is a *uniform limit of classical solutions*
`u k` of `σ₂ = 1` with `Δu k > 0` and uniform sup-norm bounds — the situation produced by
`Submission.MasterEstimate.extraction`.  The weighted estimate is applied to the classical
solutions `u k` (via `Submission.classical_weighted_estimate`, which reduces it to Trudinger's
classical interior gradient estimate `Submission.InteriorGradientBound`) and the resulting
inequality is passed to the limit.
-/
import Mathlib
import Submission.AlexandrovInputs
import Submission.AlexandrovQuad
import Submission.AffineInvariance
import Submission.WeightedGradientReduction
import Submission.Commons.Analysis.InnerProductSpace.abs_bilin_sub_le

open HessianEstimates
open Laplacian Metric MeasureTheory Set Filter
open Commons.Analysis.Calculus.FDeriv
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The volume of a ball in `ℝ⁴`. -/
theorem volume_ball_four' (x : ℝ⁴) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball x r)).toReal = r ^ 4 * (volume (ball (0 : ℝ⁴) 1)).toReal := by
  rw [← measureReal_def]
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume x r]
  rw [Measure.addHaar_real_closedBall volume x hr, finrank_euclideanSpace, Fintype.card_fin]
  rw [measureReal_def]

/-- The purely algebraic core of the slope estimate (a copy of the private
`Submission.AlexandrovSlope.slope_alg`). -/
private theorem slope_alg' {C ω A I V r Qn Ig : ℝ}
    (hC : 0 < C) (hω : 0 < ω) (hr : 0 < r) (hI : 0 ≤ I)
    (hIg : Ig ≤ I + 4 * Qn * r ^ 2 * V)
    (hV : V = 16 * r ^ 4 * ω)
    (hA1 : 16 * C * ω ≤ A) (hA2 : 64 * C * Qn * ω + 2 * Qn ≤ A) :
    C * Ig / r ^ 5 + 2 * Qn * r ≤ A / r * (I / V) + A * r := by
  subst hV
  have hr5 : (0:ℝ) < r ^ 5 := by positivity
  have h1 : C * Ig / r ^ 5 ≤ C * I / r ^ 5 + 64 * C * Qn * ω * r := by
    have h2 : C * Ig ≤ C * (I + 4 * Qn * r ^ 2 * (16 * r ^ 4 * ω)) :=
      mul_le_mul_of_nonneg_left hIg hC.le
    have h3 : C * (I + 4 * Qn * r ^ 2 * (16 * r ^ 4 * ω)) / r ^ 5
        = C * I / r ^ 5 + 64 * C * Qn * ω * r := by
      field_simp
      ring
    rw [← h3]
    exact div_le_div_of_nonneg_right h2 hr5.le
  have h4 : C * I / r ^ 5 ≤ A / r * (I / (16 * r ^ 4 * ω)) := by
    have hbase : 16 * C * ω * I ≤ A * I := mul_le_mul_of_nonneg_right hA1 hI
    have hX : A / r * (I / (16 * r ^ 4 * ω)) * r ^ 5 = A * I / (16 * ω) := by
      field_simp
    rw [div_le_iff₀ hr5, hX, le_div_iff₀ (by positivity : (0:ℝ) < 16 * ω)]
    nlinarith [hbase]
  have h5 : 64 * C * Qn * ω * r + 2 * Qn * r ≤ A * r := by nlinarith [hA2, hr]
  linarith [h1, h4, h5]

/-- **The pointwise slope estimate `(point)` for a uniform limit of classical solutions.**

`g` is the uniform limit, on `closedBall 0 3`, of `C³` solutions `u k` of `σ₂ = 1` with `Δu k > 0`
and `|u k| ≤ B`; then the second order Taylor remainder `h = taylorRemainder g G M x₀` satisfies
`|h y - h z| / |y - z| ≤ A/r * ⨍_{B(x₀,2r)} |h| + A r` for `2r < 3 - ‖x₀‖`. -/
theorem point_estimate_limit (hIG : InteriorGradientBound)
    {g : ℝ⁴ → ℝ} {u : ℕ → ℝ⁴ → ℝ} {G : ℝ⁴ → ℝ⁴} {M : Fin 4 → Fin 4 → ℝ⁴ → ℝ}
    (x₀ : ℝ⁴) {B : ℝ}
    (hgcont : ContinuousOn g (closedBall 0 3))
    (hC3 : ∀ k, ContDiffOn ℝ 3 (u k) (ball 0 3))
    (hσ : ∀ k z, z ∈ ball 0 3 → σ₂ (H (u k) (ball 0 3) z) = 1)
    (hΔ : ∀ k z, z ∈ ball 0 3 → 0 < (Δ (u k)) z)
    (hb : ∀ k z, z ∈ closedBall 0 3 → |u k z| ≤ B)
    (hconv : ∀ δ > 0, ∀ᶠ k in atTop, ∀ z ∈ closedBall 0 3, |u k z - g z| < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 < r → 2 * r < 3 - ‖x₀‖ →
      ∀ y ∈ closedBall x₀ r, ∀ z ∈ closedBall x₀ r, y ≠ z →
        |taylorRemainder g G M x₀ y - taylorRemainder g G M x₀ z| / dist y z
          ≤ A / r * ((∫ w in ball x₀ (2 * r), |taylorRemainder g G M x₀ w|) /
              (volume (ball x₀ (2 * r))).toReal) + A * r := by
  obtain ⟨C, hCpos, hCw⟩ := classical_weighted_estimate hIG
  set Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ := quadM M x₀ with hQ
  set ω : ℝ := (volume (ball (0 : ℝ⁴) 1)).toReal with hω
  have hωpos : 0 < ω := by
    rw [hω, ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_ball_pos volume 0 one_pos,
      lt_of_le_of_lt (measure_mono ball_subset_closedBall)
        (isCompact_closedBall (0 : ℝ⁴) 1).measure_lt_top⟩
  have hQnn : 0 ≤ ‖Q‖ := norm_nonneg Q
  set A : ℝ := 16 * C * ω + 64 * C * ‖Q‖ * ω + 2 * ‖Q‖ + 1 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hA1 : 16 * C * ω ≤ A := by rw [hA]; nlinarith [hCpos, hωpos, hQnn]
  have hA2 : 64 * C * ‖Q‖ * ω + 2 * ‖Q‖ ≤ A := by rw [hA]; nlinarith [hCpos, hωpos, hQnn]
  refine ⟨A, hApos, ?_⟩
  intro r hr hrR y hy z hz hyz
  have hsub : closedBall x₀ (2 * r) ⊆ ball 0 3 := by
    intro v hv
    rw [mem_ball, dist_zero_right]
    have hv' : dist v x₀ ≤ 2 * r := by rwa [mem_closedBall] at hv
    have h1 : dist v 0 ≤ dist v x₀ + dist x₀ 0 := dist_triangle _ _ _
    rw [dist_zero_right v, dist_zero_right x₀] at h1
    linarith
  have hBnn : 0 ≤ B := le_trans (abs_nonneg (u 0 0)) (hb 0 0 (by simp))
  have hpt : ∀ w ∈ closedBall (0:ℝ⁴) 3, Tendsto (fun k => u k w) atTop (𝓝 (g w)) := by
    intro w hw
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h' := hconv ε hε
    rw [Filter.eventually_atTop] at h'
    obtain ⟨k0, hk0⟩ := h'
    exact ⟨k0, fun k hk => by
      have h3 := hk0 k hk w hw
      rw [Real.dist_eq]
      exact h3⟩
  set L : ℝ⁴ →L[ℝ] ℝ := innerSL ℝ (G x₀) with hL
  set c : ℕ → ℝ := fun k => u k x₀ - L x₀ with hc
  set gp : ℕ → ℝ⁴ → ℝ := fun k w => u k w - (c k + L w) with hgp
  have hgp_eq : ∀ k w, gp k w = taylorRemainder (u k) G M x₀ w
      + quadM M x₀ (w - x₀) (w - x₀) := by
    intro k w
    rw [hgp, hc, hL, taylorRemainder_eq, map_sub]
    ring
  have hx₀3 : x₀ ∈ closedBall (0:ℝ⁴) 3 := by
    rw [mem_closedBall, dist_zero_right]
    have h : 0 < 3 - ‖x₀‖ := by linarith [norm_nonneg x₀]
    linarith
  -- ## the weighted estimate for each `g'_k`
  have hM₀ : (0:ℝ) ≤ 2 * B + 3 * ‖L‖ := by nlinarith [hBnn, norm_nonneg L]
  have hGE : ∀ k, r ^ 5 * |gp k y - gp k z| / dist y z
      ≤ C * ∫ w in ball x₀ (2 * r), |gp k w| := by
    intro k
    have hk3 : ContDiffOn ℝ 3 (u k) (ball 0 3) := hC3 k
    have hcont : ContDiffOn ℝ 3 (gp k) (ball x₀ (2 * r)) := by
      rw [hgp]
      exact hk3.mono (fun w hw => hsub (ball_subset_closedBall hw)) |>.sub (by fun_prop)
    have hσ2 : ∀ w ∈ ball x₀ (2 * r), σ₂ (H (gp k) (ball x₀ (2 * r)) w) = 1 := by
      intro w hw
      have hw3 : w ∈ ball (0:ℝ⁴) 3 := hsub (ball_subset_closedBall hw)
      rw [hgp]
      rw [sigma2_sub_affine (isOpen_ball.mem_nhds hw)
        (((hk3.contDiffAt (isOpen_ball.mem_nhds hw3)).of_le
          (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffWithinAt) (c k) L]
      rw [H_congr_of_mem_nhds (isOpen_ball.mem_nhds hw) (isOpen_ball.mem_nhds hw3)]
      exact hσ k w hw3
    have hΔ2 : ∀ w ∈ ball x₀ (2 * r), 0 < (Δ (gp k)) w := by
      intro w hw
      have hw3 : w ∈ ball (0:ℝ⁴) 3 := hsub (ball_subset_closedBall hw)
      rw [hgp]
      rw [laplacian_sub_affine isOpen_ball hw3 hk3 (c k) L]
      exact hΔ k w hw3
    have hbd2 : ∀ w ∈ ball x₀ (2 * r), |gp k w| ≤ 2 * B + 3 * ‖L‖ := by
      intro w hw
      have hw3 : w ∈ closedBall (0:ℝ⁴) 3 :=
        ball_subset_closedBall (hsub (ball_subset_closedBall hw))
      obtain ⟨hwa, hwb⟩ := abs_le.mp (hb k w hw3)
      obtain ⟨hxa, hxb⟩ := abs_le.mp (hb k x₀ hx₀3)
      have hdw : dist w x₀ < 3 := by rw [mem_ball] at hw; linarith [norm_nonneg x₀]
      rw [hgp]
      simp only
      have hLw : |L (w - x₀)| ≤ ‖L‖ * 3 := by
        have h1 : ‖L (w - x₀)‖ ≤ ‖L‖ * ‖w - x₀‖ := L.le_opNorm (w - x₀)
        rw [Real.norm_eq_abs, ← dist_eq_norm] at h1
        exact le_trans h1 (mul_le_mul_of_nonneg_left hdw.le (norm_nonneg L))
      calc |u k w - (c k + L w)| = |u k w - u k x₀ - L (w - x₀)| := by
            rw [hc]; simp only [map_sub]; ring_nf
        _ ≤ |u k w - u k x₀| + |L (w - x₀)| := by
            have h := abs_add_le (u k w - u k x₀) (-(L (w - x₀)))
            rw [abs_neg] at h
            exact h
        _ ≤ 2 * B + ‖L‖ * 3 := by
            refine add_le_add ?_ hLw
            rw [abs_sub_le_iff]
            exact ⟨by linarith, by linarith⟩
        _ = 2 * B + 3 * ‖L‖ := by ring
    exact hCw (gp k) x₀ r (2 * B + 3 * ‖L‖) hr hM₀ hcont hσ2 hΔ2 hbd2 y hy z hz hyz
  -- ## the Taylor remainders
  set d : ℝ := dist y z with hd
  have hdpos : 0 < d := by rw [hd]; exact dist_pos.mpr hyz
  set hfun : ℕ → ℝ⁴ → ℝ := fun k w => taylorRemainder (u k) G M x₀ w with hhfun
  set hlim : ℝ⁴ → ℝ := fun w => taylorRemainder g G M x₀ w with hhlim
  have hcq : Continuous (fun w : ℝ⁴ => Q (w - x₀) (w - x₀)) := by fun_prop
  have hfuneq : ∀ k, hfun k = fun w => gp k w - Q (w - x₀) (w - x₀) := by
    intro k
    funext w
    rw [hgp_eq k w]
    ring
  have hcont_gp_k : ∀ k, ContinuousOn (gp k) (ball x₀ (2 * r)) := by
    intro k
    rw [hgp]
    exact ((hC3 k).continuousOn.mono (fun w hw => hsub (ball_subset_closedBall hw))).sub
      (by fun_prop)
  have hcont_h_k : ∀ k, ContinuousOn (hfun k) (ball x₀ (2 * r)) := by
    intro k
    rw [hfuneq k]
    exact (hcont_gp_k k).sub hcq.continuousOn
  have hcont_gp_c : ∀ k, ContinuousOn (gp k) (closedBall x₀ (2 * r)) := by
    intro k
    rw [hgp]
    exact ((hC3 k).continuousOn.mono (fun w hw => hsub hw)).sub (by fun_prop)
  have hint_gp_k : ∀ k, IntegrableOn (fun w => |gp k w|) (ball x₀ (2 * r)) volume := fun k =>
    (((hcont_gp_c k).abs).integrableOn_compact (isCompact_closedBall x₀ (2 * r))).mono_set
      ball_subset_closedBall
  have hcont_h_c : ∀ k, ContinuousOn (hfun k) (closedBall x₀ (2 * r)) := by
    intro k
    rw [hfuneq k]
    exact (hcont_gp_c k).sub (hcq.continuousOn)
  have hint_h_k : ∀ k, IntegrableOn (fun w => |hfun k w|) (ball x₀ (2 * r)) volume := fun k =>
    (((hcont_h_c k).abs).integrableOn_compact (isCompact_closedBall x₀ (2 * r))).mono_set
      ball_subset_closedBall
  have hqd : |Q (y - x₀) (y - x₀) - Q (z - x₀) (z - x₀)| ≤ 2 * ‖Q‖ * r * d := by
    rw [hd]
    have h1 := Commons.Analysis.InnerProductSpace.abs_bilin_sub_le Q (y - x₀) (z - x₀)
    have hyr : ‖y - x₀‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.mp hy
    have hzr : ‖z - x₀‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.mp hz
    have hdist : ‖(y - x₀) - (z - x₀)‖ = dist y z := by
      rw [dist_eq_norm]; congr 1; abel
    rw [hdist] at h1
    have h3 : ‖y - x₀‖ + ‖z - x₀‖ ≤ 2 * r := by linarith
    have h4 : ‖Q‖ * (‖y - x₀‖ + ‖z - x₀‖) ≤ ‖Q‖ * (2 * r) :=
      mul_le_mul_of_nonneg_left h3 hQnn
    have h5 : ‖Q‖ * (‖y - x₀‖ + ‖z - x₀‖) * dist y z ≤ ‖Q‖ * (2 * r) * dist y z :=
      mul_le_mul_of_nonneg_right h4 dist_nonneg
    linarith [h1, h5]
  -- ## the per-`k` slope estimate
  have hperk : ∀ k, |hfun k y - hfun k z| / d
      ≤ A / r * ((∫ w in ball x₀ (2 * r), |hfun k w|)
          / (volume (ball x₀ (2 * r))).toReal) + A * r := by
    intro k
    set Ig : ℝ := ∫ w in ball x₀ (2 * r), |gp k w| with hIg
    set I : ℝ := ∫ w in ball x₀ (2 * r), |hfun k w| with hI
    set V : ℝ := (volume (ball x₀ (2 * r))).toReal with hV
    have hVval : V = 16 * r ^ 4 * ω := by
      rw [hV, hω, volume_ball_four' x₀ (by positivity : (0:ℝ) ≤ 2 * r)]
      ring
    have hInn : 0 ≤ I := by rw [hI]; exact integral_nonneg fun w => abs_nonneg _
    have hint_gp : IntegrableOn (fun w => |gp k w|) (ball x₀ (2 * r)) volume := hint_gp_k k
    have hint_h : IntegrableOn (fun w => |hfun k w|) (ball x₀ (2 * r)) volume := hint_h_k k
    have hint_q : IntegrableOn (fun w => |Q (w - x₀) (w - x₀)|) (ball x₀ (2 * r)) volume :=
      (hcq.abs.continuousOn.integrableOn_compact (isCompact_closedBall x₀ (2 * r))).mono_set
        ball_subset_closedBall
    have hIg_le : Ig ≤ I + 4 * ‖Q‖ * r ^ 2 * V := by
      rw [hIg, hI, hV]
      have h1 : ∫ w in ball x₀ (2 * r), |gp k w|
          ≤ ∫ w in ball x₀ (2 * r), (|hfun k w| + |Q (w - x₀) (w - x₀)|) := by
        refine setIntegral_mono_on hint_gp (hint_h.add hint_q) measurableSet_ball ?_
        intro w _
        rw [hgp_eq k w, ← hQ]
        exact abs_add_le _ _
      have h2 : ∫ w in ball x₀ (2 * r), (|hfun k w| + |Q (w - x₀) (w - x₀)|)
          = (∫ w in ball x₀ (2 * r), |hfun k w|)
            + ∫ w in ball x₀ (2 * r), |Q (w - x₀) (w - x₀)| :=
        integral_add hint_h hint_q
      have h3 : ∫ w in ball x₀ (2 * r), |Q (w - x₀) (w - x₀)|
          ≤ (4 * ‖Q‖ * r ^ 2) * (volume (ball x₀ (2 * r))).toReal := by
        have hconst : ∫ w in ball x₀ (2 * r), (4 * ‖Q‖ * r ^ 2)
            = (4 * ‖Q‖ * r ^ 2) * (volume (ball x₀ (2 * r))).toReal := by
          rw [setIntegral_const, measureReal_def, smul_eq_mul]
          ring
        rw [← hconst]
        refine setIntegral_mono_on hint_q (((continuous_const :
          Continuous (fun _ : ℝ⁴ => 4 * ‖Q‖ * r ^ 2)).continuousOn).integrableOn_compact
            (isCompact_closedBall x₀ (2 * r)) (μ := volume) |>.mono_set ball_subset_closedBall)
          measurableSet_ball ?_
        intro w hw
        rw [mem_ball, dist_eq_norm] at hw
        have hQw : |Q (w - x₀) (w - x₀)| ≤ ‖Q‖ * ‖w - x₀‖ ^ 2 := by
          have h1 : ‖Q (w - x₀) (w - x₀)‖ ≤ ‖Q (w - x₀)‖ * ‖w - x₀‖ :=
            (Q (w - x₀)).le_opNorm (w - x₀)
          have h2 : ‖Q (w - x₀)‖ ≤ ‖Q‖ * ‖w - x₀‖ := Q.le_opNorm (w - x₀)
          have h3 : ‖Q (w - x₀)‖ * ‖w - x₀‖ ≤ (‖Q‖ * ‖w - x₀‖) * ‖w - x₀‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
          rw [Real.norm_eq_abs] at h1
          nlinarith [h1, h3]
        have h4 : ‖w - x₀‖ ^ 2 ≤ (2 * r) ^ 2 := by
          nlinarith [hw, norm_nonneg (w - x₀), hr]
        calc |Q (w - x₀) (w - x₀)| ≤ ‖Q‖ * ‖w - x₀‖ ^ 2 := hQw
          _ ≤ ‖Q‖ * (2 * r) ^ 2 := mul_le_mul_of_nonneg_left h4 hQnn
          _ = 4 * ‖Q‖ * r ^ 2 := by ring
      rw [h2] at h1
      linarith [h1, h3]
    have hgd : |gp k y - gp k z| ≤ C * Ig * d / r ^ 5 := by
      have h1 : r ^ 5 * |gp k y - gp k z| / d ≤ C * Ig := by
        rw [hIg, hd]
        exact hGE k
      rw [div_le_iff₀ hdpos] at h1
      rw [le_div_iff₀ (by positivity : (0:ℝ) < r ^ 5)]
      linarith [h1]
    have hhd : |hfun k y - hfun k z| ≤ |gp k y - gp k z|
        + |Q (y - x₀) (y - x₀) - Q (z - x₀) (z - x₀)| := by
      have e1 : hfun k y = gp k y - Q (y - x₀) (y - x₀) := by
        rw [hgp_eq k y]; ring
      have e2 : hfun k z = gp k z - Q (z - x₀) (z - x₀) := by
        rw [hgp_eq k z]; ring
      rw [e1, e2]
      have e3 : (gp k y - Q (y - x₀) (y - x₀)) - (gp k z - Q (z - x₀) (z - x₀))
          = (gp k y - gp k z) - (Q (y - x₀) (y - x₀) - Q (z - x₀) (z - x₀)) := by ring
      rw [e3]
      calc |(gp k y - gp k z) - (Q (y - x₀) (y - x₀) - Q (z - x₀) (z - x₀))|
          = dist (gp k y - gp k z) (Q (y - x₀) (y - x₀) - Q (z - x₀) (z - x₀)) := by
            rw [Real.dist_eq]
        _ ≤ dist (gp k y - gp k z) 0
            + dist 0 (Q (y - x₀) (y - x₀) - Q (z - x₀) (z - x₀)) := dist_triangle _ _ _
        _ = |gp k y - gp k z| + |Q (y - x₀) (y - x₀) - Q (z - x₀) (z - x₀)| := by
            rw [Real.dist_eq, Real.dist_eq, sub_zero, zero_sub, abs_neg]
    have hstep1 : |hfun k y - hfun k z| / d ≤ C * Ig / r ^ 5 + 2 * ‖Q‖ * r := by
      rw [div_le_iff₀ hdpos]
      calc |hfun k y - hfun k z|
          ≤ |gp k y - gp k z| + |Q (y - x₀) (y - x₀) - Q (z - x₀) (z - x₀)| := hhd
        _ ≤ C * Ig * d / r ^ 5 + 2 * ‖Q‖ * r * d := by linarith [hgd, hqd]
        _ = (C * Ig / r ^ 5 + 2 * ‖Q‖ * r) * d := by ring
    exact le_trans hstep1 (slope_alg' hCpos hωpos hr hInn hIg_le hVval hA1 hA2)
  -- ## passage to the limit
  have hlim_pt : ∀ w ∈ ball x₀ (2 * r), Tendsto (fun k => hfun k w) atTop (𝓝 (hlim w)) := by
    intro w hw
    have hw3 : w ∈ closedBall (0:ℝ⁴) 3 := ball_subset_closedBall (hsub (ball_subset_closedBall hw))
    have h1 : Tendsto (fun k => u k w - g w) atTop (𝓝 (g w - g w)) :=
      (hpt w hw3).sub tendsto_const_nhds
    have h2 : Tendsto (fun k => u k x₀ - g x₀) atTop (𝓝 (g x₀ - g x₀)) :=
      (hpt x₀ hx₀3).sub tendsto_const_nhds
    have h3 : (fun k => hfun k w) = fun k => (u k w - g w) - (u k x₀ - g x₀) + hlim w := by
      funext k
      simp only [hhfun, hhlim, taylorRemainder_eq]
      ring
    rw [h3]
    have hc : Tendsto (fun _ : ℕ => hlim w) atTop (𝓝 (hlim w)) := tendsto_const_nhds
    have h4 := (h1.sub h2).add hc
    simpa using h4
  have hgball : ContinuousOn g (ball x₀ (2 * r)) :=
    hgcont.mono (fun w hw => ball_subset_closedBall (hsub (ball_subset_closedBall hw)))
  have hgball_c : ContinuousOn g (closedBall x₀ (2 * r)) :=
    hgcont.mono (fun w hw => ball_subset_closedBall (hsub hw))
  have hlim_eq : hlim = fun w => g w - g x₀ - (innerSL ℝ (G x₀)) (w - x₀)
      - Q (w - x₀) (w - x₀) := by
    funext w
    simp only [hhlim, taylorRemainder_eq, hQ]
  have hcont_hlim_c : ContinuousOn hlim (closedBall x₀ (2 * r)) := by
    rw [hlim_eq]
    refine ContinuousOn.sub (ContinuousOn.sub (ContinuousOn.sub hgball_c continuousOn_const) ?_) ?_
    · fun_prop
    · fun_prop
  have hcont_hlim : ContinuousOn hlim (ball x₀ (2 * r)) :=
    hcont_hlim_c.mono ball_subset_closedBall
  have hint_hlim : IntegrableOn (fun w => |hlim w|) (ball x₀ (2 * r)) volume :=
    ((hcont_hlim_c.abs).integrableOn_compact (isCompact_closedBall x₀ (2 * r))).mono_set
      ball_subset_closedBall
  have hlim_int : Tendsto (fun k => ∫ w in ball x₀ (2 * r), |hfun k w|) atTop
      (𝓝 (∫ w in ball x₀ (2 * r), |hlim w|)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set V : ℝ := (volume (ball x₀ (2 * r))).toReal with hV
    have hVpos : 0 < V := by
      rw [hV, ENNReal.toReal_pos_iff]
      exact ⟨Metric.measure_ball_pos volume x₀ (by positivity),
        lt_of_le_of_lt (measure_mono ball_subset_closedBall)
          (isCompact_closedBall x₀ (2 * r)).measure_lt_top⟩
    have hδpos : 0 < ε / (2 * (V + 1)) := by positivity
    have h' := hconv (ε / (2 * (V + 1))) hδpos
    rw [Filter.eventually_atTop] at h'
    obtain ⟨k0, hk0⟩ := h'
    refine ⟨k0, fun k hk => ?_⟩
    have hptw : ∀ w ∈ ball x₀ (2 * r), |hfun k w - hlim w| ≤ ε / (V + 1) := by
      intro w hw
      have hw3 : w ∈ closedBall (0:ℝ⁴) 3 := ball_subset_closedBall (hsub (ball_subset_closedBall hw))
      have h1 := hk0 k hk w hw3
      have h2 := hk0 k hk x₀ hx₀3
      have h3 : hfun k w - hlim w = (u k w - g w) - (u k x₀ - g x₀) := by
        rw [show hfun k w = taylorRemainder (u k) G M x₀ w from rfl,
          show hlim w = taylorRemainder g G M x₀ w from rfl,
          taylorRemainder_eq, taylorRemainder_eq]
        ring
      have h4 : ε / (2 * (V + 1)) + ε / (2 * (V + 1)) = ε / (V + 1) := by
        field_simp
        ring
      rw [h3]
      refine le_trans ?_ (le_of_eq h4)
      calc |(u k w - g w) - (u k x₀ - g x₀)| ≤ |u k w - g w| + |u k x₀ - g x₀| := by
            have h := abs_add_le (u k w - g w) (-(u k x₀ - g x₀))
            rw [abs_neg] at h
            exact h
        _ ≤ ε / (2 * (V + 1)) + ε / (2 * (V + 1)) := add_le_add h1.le h2.le
    have hint1 : IntegrableOn (fun w => |hfun k w|) (ball x₀ (2 * r)) volume := hint_h_k k
    have hintdiff : IntegrableOn (fun w => |hfun k w - hlim w|) (ball x₀ (2 * r)) volume :=
      ((((hcont_h_c k).sub hcont_hlim_c).abs).integrableOn_compact
        (isCompact_closedBall x₀ (2 * r))).mono_set ball_subset_closedBall
    have hdiff : |(∫ w in ball x₀ (2 * r), |hfun k w|)
        - (∫ w in ball x₀ (2 * r), |hlim w|)|
        ≤ ∫ w in ball x₀ (2 * r), |hfun k w - hlim w| := by
      have h1 : ∫ w in ball x₀ (2 * r), (|hfun k w| - |hlim w|)
          = (∫ w in ball x₀ (2 * r), |hfun k w|)
            - ∫ w in ball x₀ (2 * r), |hlim w| := integral_sub hint1 hint_hlim
      have h2 : |∫ w in ball x₀ (2 * r), (|hfun k w| - |hlim w|)|
          ≤ ∫ w in ball x₀ (2 * r), |(|hfun k w| - |hlim w|)| :=
        abs_integral_le_integral_abs
      have h3 : ∫ w in ball x₀ (2 * r), |(|hfun k w| - |hlim w|)|
          ≤ ∫ w in ball x₀ (2 * r), |hfun k w - hlim w| := by
        refine setIntegral_mono_on (hint1.sub hint_hlim).abs hintdiff measurableSet_ball ?_
        intro w _
        exact abs_abs_sub_abs_le_abs_sub _ _
      rw [h1] at h2
      linarith [h2, h3]
    have hInt_le : ∫ w in ball x₀ (2 * r), |hfun k w - hlim w| ≤ (ε / (V + 1)) * V := by
      have hconst : ∫ w in ball x₀ (2 * r), (ε / (V + 1))
          = (ε / (V + 1)) * V := by
        rw [setIntegral_const, measureReal_def, smul_eq_mul, hV]
        ring
      rw [← hconst]
      refine setIntegral_mono_on hintdiff (((continuous_const :
        Continuous (fun _ : ℝ⁴ => ε / (V + 1))).continuousOn).integrableOn_compact
          (isCompact_closedBall x₀ (2 * r)) (μ := volume) |>.mono_set ball_subset_closedBall)
        measurableSet_ball ?_
      intro w hw
      exact hptw w hw
    have hlast : (ε / (V + 1)) * V < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < V + 1)]
      nlinarith [hε, hVpos.le]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (le_trans hdiff hInt_le) hlast
  -- ## the limit inequality
  have hy2 : y ∈ ball x₀ (2 * r) := by rw [mem_ball]; rw [mem_closedBall] at hy; linarith
  have hz2 : z ∈ ball x₀ (2 * r) := by rw [mem_ball]; rw [mem_closedBall] at hz; linarith
  have ha : Tendsto (fun k => |hfun k y - hfun k z| / d) atTop (𝓝 (|hlim y - hlim z| / d)) :=
    (((hlim_pt y hy2).sub (hlim_pt z hz2)).abs).div_const d
  have hbnd : Tendsto (fun k => A / r * ((∫ w in ball x₀ (2 * r), |hfun k w|)
        / (volume (ball x₀ (2 * r))).toReal) + A * r) atTop
      (𝓝 (A / r * ((∫ w in ball x₀ (2 * r), |hlim w|)
        / (volume (ball x₀ (2 * r))).toReal) + A * r)) := by
    have hc1 : Tendsto (fun _ : ℕ => A / r) atTop (𝓝 (A / r)) := tendsto_const_nhds
    have hc2 : Tendsto (fun _ : ℕ => A * r) atTop (𝓝 (A * r)) := tendsto_const_nhds
    have h1 : Tendsto (fun k => A / r * ((∫ w in ball x₀ (2 * r), |hfun k w|)
        / (volume (ball x₀ (2 * r))).toReal)) atTop
        (𝓝 (A / r * ((∫ w in ball x₀ (2 * r), |hlim w|)
        / (volume (ball x₀ (2 * r))).toReal))) := hc1.mul (hlim_int.div_const _)
    exact h1.add hc2
  have := le_of_tendsto_of_tendsto' ha hbnd (fun k => hperk k)
  rw [hd] at this
  exact this

end Submission

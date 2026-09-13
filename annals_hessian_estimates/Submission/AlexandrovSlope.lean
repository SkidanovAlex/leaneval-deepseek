/-
The pointwise slope estimate `(point)` in the proof of Proposition 3.1 of Shankar--Yuan: for a
continuous viscosity solution `g` of `σ₂ = 1` with `Δg ≥ 0` on `ball 0 3`, the second order Taylor
remainder `h = taylorRemainder g G M x₀` satisfies
`|h y - h z| / |y - z| ≤ A/r * ⨍_{ball x₀ (2r)} |h| + A r`
for `0 < 2r < 3 - ‖x₀‖`.  It is obtained by applying Trudinger--Wang's weighted gradient estimate
(`GradientEstimateInput`) to `g` minus its affine part at `x₀`.
-/
import Mathlib
import Submission.AlexandrovQuad
import Submission.AlexandrovInputs
import Submission.ViscosityAffine
import Submission.Commons.Analysis.InnerProductSpace.abs_bilin_sub_le

open MeasureTheory Metric Set Filter Function
open Commons.Analysis.Calculus.FDeriv
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The volume of a ball in `ℝ⁴`. -/
theorem volume_ball_four (x : ℝ⁴) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball x r)).toReal
      = r ^ 4 * (volume (ball (0 : ℝ⁴) 1)).toReal := by
  rw [← measureReal_def]
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume x r]
  rw [Measure.addHaar_real_closedBall volume x hr, finrank_euclideanSpace, Fintype.card_fin]
  rw [measureReal_def]

/-- The purely algebraic core of the slope estimate. -/
private theorem slope_alg {C ω A I V r Qn Ig : ℝ}
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

/-- **The pointwise slope estimate `(point)`**. -/
theorem point_estimate (hG : GradientEstimateInput) {g : ℝ⁴ → ℝ} {G : ℝ⁴ → ℝ⁴}
    {M : Fin 4 → Fin 4 → ℝ⁴ → ℝ}
    (hgcont : ContinuousOn g (closedBall 0 3))
    (hgsol : IsViscSolution (fun N => -Gop N) g (ball 0 3))
    (hgΔ : IsViscSubsolution negTrace g (ball 0 3))
    (x₀ : ℝ⁴) :
    ∃ A : ℝ, 0 < A ∧
      ∀ r : ℝ, 0 < r → 2 * r < 3 - ‖x₀‖ →
        ∀ y ∈ closedBall x₀ r, ∀ z ∈ closedBall x₀ r, y ≠ z →
        |taylorRemainder g G M x₀ y - taylorRemainder g G M x₀ z| / dist y z
          ≤ A / r * ((∫ w in ball x₀ (2 * r), |taylorRemainder g G M x₀ w|) /
              (volume (ball x₀ (2 * r))).toReal) + A * r := by
  obtain ⟨C, hCpos, hC⟩ := hG
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
  -- ## the larger ball lies in `ball 0 3`
  have hsub : closedBall x₀ (2 * r) ⊆ ball 0 3 := by
    intro v hv
    rw [mem_ball, dist_zero_right]
    have hv' : dist v x₀ ≤ 2 * r := by rwa [mem_closedBall] at hv
    have h1 : dist v 0 ≤ dist v x₀ + dist x₀ 0 := dist_triangle _ _ _
    rw [dist_zero_right v, dist_zero_right x₀] at h1
    linarith
  -- ## the affine subtraction
  set L : ℝ⁴ →L[ℝ] ℝ := innerSL ℝ (G x₀) with hL
  set c : ℝ := g x₀ - L x₀ with hc
  set g' : ℝ⁴ → ℝ := fun y => g y - (c + L y) with hg'
  have hgp : ∀ y : ℝ⁴, g' y = g y - g x₀ - L (y - x₀) := by
    intro y
    rw [hg', hc, hL, map_sub]
    ring
  have hcont' : ContinuousOn g' (ball 0 3) := by
    rw [hg']
    exact (hgcont.mono ball_subset_closedBall).sub
      (continuous_const.add L.continuous).continuousOn
  have hsol' : IsViscSolution (fun N => -Gop N) g' (ball 0 3) :=
    isViscSolution_sub_affine isOpen_ball hgsol L c
  have hΔ' : IsViscSubsolution negTrace g' (ball 0 3) :=
    isViscSubsolution_sub_affine isOpen_ball hgΔ L c
  have hGEyz : r ^ 5 * |g' y - g' z| / dist y z ≤
      C * ∫ w in ball x₀ (2 * r), |g' w| :=
    hC g' (ball 0 3) isOpen_ball hcont' hsol' hΔ' x₀ r hr hsub y hy z hz hyz
  -- ## continuity
  have hhcont : ContinuousOn (fun y : ℝ⁴ => taylorRemainder g G M x₀ y) (ball 0 3) := by
    have hg1 : ContinuousOn g (ball 0 3) := hgcont.mono ball_subset_closedBall
    have h2 : (fun y : ℝ⁴ => taylorRemainder g G M x₀ y)
        = fun y : ℝ⁴ => g y - (g x₀ + L (y - x₀) + quadM M x₀ (y - x₀) (y - x₀)) := by
      funext y
      rw [taylorRemainder_eq, ← hL]
      ring
    rw [h2]
    exact hg1.sub (by fun_prop)
  have hqcont : ContinuousOn (fun w : ℝ⁴ => quadM M x₀ (w - x₀) (w - x₀)) (ball 0 3) := by
    fun_prop
  -- ## integrability on the ball of radius `2r`
  have hIntOn : ∀ (f : ℝ⁴ → ℝ), ContinuousOn f (ball 0 3) →
      IntegrableOn f (ball x₀ (2 * r)) volume := by
    intro f hf
    exact ((hf.mono hsub).integrableOn_compact (isCompact_closedBall x₀ (2 * r))).mono_set
      ball_subset_closedBall
  have hIntAbs : ∀ (f : ℝ⁴ → ℝ), ContinuousOn f (ball 0 3) →
      Integrable (fun w : ℝ⁴ => |f w|) (volume.restrict (ball x₀ (2 * r))) := by
    intro f hf
    simpa only [Real.norm_eq_abs] using (hIntOn f hf).norm
  -- ## the abbreviations
  set d : ℝ := dist y z with hd
  have hdpos : 0 < d := by rw [hd]; exact dist_pos.mpr hyz
  set I : ℝ := ∫ w in ball x₀ (2 * r), |taylorRemainder g G M x₀ w| with hI
  set V : ℝ := (volume (ball x₀ (2 * r))).toReal with hV
  set Ig : ℝ := ∫ w in ball x₀ (2 * r), |g' w| with hIg
  have hVval : V = 16 * r ^ 4 * ω := by
    rw [hV, hω, volume_ball_four x₀ (by positivity : (0:ℝ) ≤ 2 * r)]
    ring
  have hInn : 0 ≤ I := by
    rw [hI]
    exact integral_nonneg fun w => abs_nonneg _
  -- ## the pointwise relation between `g'`, `h` and the quadratic form
  have hgp_q : ∀ w : ℝ⁴, g' w = taylorRemainder g G M x₀ w
      + quadM M x₀ (w - x₀) (w - x₀) := by
    intro w
    rw [hgp w, taylorRemainder_eq, ← hL]
    ring
  -- ## the integral of `|g'|` is bounded by the integral of `|h|` plus the volume term
  have hIg_le : Ig ≤ I + 4 * ‖Q‖ * r ^ 2 * V := by
    rw [hIg, hI, hV]
    have h1 : ∫ w in ball x₀ (2 * r), |g' w|
        ≤ ∫ w in ball x₀ (2 * r),
            (|taylorRemainder g G M x₀ w| + |quadM M x₀ (w - x₀) (w - x₀)|) := by
      refine setIntegral_mono_on (hIntAbs g' hcont') ?_ measurableSet_ball ?_
      · exact (hIntAbs _ hhcont).add (hIntAbs _ hqcont)
      · intro w _
        rw [hgp_q w]
        exact abs_add_le _ _
    have h2 : ∫ w in ball x₀ (2 * r),
          (|taylorRemainder g G M x₀ w| + |quadM M x₀ (w - x₀) (w - x₀)|)
        = (∫ w in ball x₀ (2 * r), |taylorRemainder g G M x₀ w|)
          + ∫ w in ball x₀ (2 * r), |quadM M x₀ (w - x₀) (w - x₀)| :=
      integral_add (hIntAbs _ hhcont) (hIntAbs _ hqcont)
    have h3 : ∫ w in ball x₀ (2 * r), |quadM M x₀ (w - x₀) (w - x₀)|
        ≤ (4 * ‖Q‖ * r ^ 2) * (volume (ball x₀ (2 * r))).toReal := by
      have hconst : ∫ w in ball x₀ (2 * r), (4 * ‖Q‖ * r ^ 2)
          = (4 * ‖Q‖ * r ^ 2) * (volume (ball x₀ (2 * r))).toReal := by
        rw [setIntegral_const, measureReal_def, smul_eq_mul]
        ring
      rw [← hconst]
      refine setIntegral_mono_on (hIntAbs _ hqcont) ?_ measurableSet_ball ?_
      · exact ((continuous_const.continuousOn.mono hsub :
            ContinuousOn (fun _ : ℝ⁴ => 4 * ‖Q‖ * r ^ 2) (closedBall x₀ (2 * r))).integrableOn_compact
          (isCompact_closedBall x₀ (2 * r))).mono_set ball_subset_closedBall
      · intro w hw
        rw [mem_ball, dist_eq_norm] at hw
        have hQw : |quadM M x₀ (w - x₀) (w - x₀)| ≤ ‖Q‖ * ‖w - x₀‖ ^ 2 := by
          rw [← hQ]
          have h1 : ‖Q (w - x₀) (w - x₀)‖ ≤ ‖Q (w - x₀)‖ * ‖w - x₀‖ :=
            (Q (w - x₀)).le_opNorm (w - x₀)
          have h2 : ‖Q (w - x₀)‖ ≤ ‖Q‖ * ‖w - x₀‖ := Q.le_opNorm (w - x₀)
          have h3 : ‖Q (w - x₀)‖ * ‖w - x₀‖ ≤ (‖Q‖ * ‖w - x₀‖) * ‖w - x₀‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
          rw [Real.norm_eq_abs] at h1
          nlinarith [h1, h3]
        have h4 : ‖w - x₀‖ ^ 2 ≤ (2 * r) ^ 2 := by
          nlinarith [hw, norm_nonneg (w - x₀), hr]
        calc |quadM M x₀ (w - x₀) (w - x₀)| ≤ ‖Q‖ * ‖w - x₀‖ ^ 2 := hQw
          _ ≤ ‖Q‖ * (2 * r) ^ 2 := mul_le_mul_of_nonneg_left h4 hQnn
          _ = 4 * ‖Q‖ * r ^ 2 := by ring
    rw [h2] at h1
    linarith [h1, h3]
  -- ## the quadratic form difference
  have hqd : |quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀)|
      ≤ 2 * ‖Q‖ * r * d := by
    rw [← hQ, hd]
    have h1 := Commons.Analysis.InnerProductSpace.abs_bilin_sub_le Q (y - x₀) (z - x₀)
    have hyr : ‖y - x₀‖ ≤ r := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hy
    have hzr : ‖z - x₀‖ ≤ r := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hz
    have hdist : ‖(y - x₀) - (z - x₀)‖ = dist y z := by
      rw [dist_eq_norm]
      congr 1
      abel
    rw [hdist] at h1
    have h3 : ‖y - x₀‖ + ‖z - x₀‖ ≤ 2 * r := by linarith
    have h4 : ‖Q‖ * (‖y - x₀‖ + ‖z - x₀‖) ≤ ‖Q‖ * (2 * r) :=
      mul_le_mul_of_nonneg_left h3 hQnn
    have h5 : ‖Q‖ * (‖y - x₀‖ + ‖z - x₀‖) * dist y z ≤ ‖Q‖ * (2 * r) * dist y z :=
      mul_le_mul_of_nonneg_right h4 dist_nonneg
    linarith [h1, h5]
  -- ## the gradient estimate in the form we need
  have hgd : |g' y - g' z| ≤ C * Ig * d / r ^ 5 := by
    have h1 : r ^ 5 * |g' y - g' z| / d ≤ C * Ig := by
      rw [hIg, hd]
      exact hGEyz
    rw [div_le_iff₀ hdpos] at h1
    rw [le_div_iff₀ (by positivity : (0:ℝ) < r ^ 5)]
    linarith [h1]
  -- ## the Taylor remainder difference
  have hhd : |taylorRemainder g G M x₀ y - taylorRemainder g G M x₀ z|
      ≤ |g' y - g' z|
        + |quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀)| := by
    have e1 : taylorRemainder g G M x₀ y = g' y - quadM M x₀ (y - x₀) (y - x₀) := by
      rw [hgp_q y]; ring
    have e2 : taylorRemainder g G M x₀ z = g' z - quadM M x₀ (z - x₀) (z - x₀) := by
      rw [hgp_q z]; ring
    rw [e1, e2]
    have e3 : (g' y - quadM M x₀ (y - x₀) (y - x₀))
          - (g' z - quadM M x₀ (z - x₀) (z - x₀))
        = (g' y - g' z)
          - (quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀)) := by ring
    rw [e3]
    rw [show |(g' y - g' z) - (quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀))|
        = dist (g' y - g' z)
            (quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀)) by
      rw [Real.dist_eq]]
    calc dist (g' y - g' z) (quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀))
        ≤ dist (g' y - g' z) 0
          + dist 0 (quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀)) :=
          dist_triangle _ _ _
      _ = |g' y - g' z| + |quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀)| := by
          rw [Real.dist_eq, Real.dist_eq, sub_zero, zero_sub, abs_neg]
  -- ## putting everything together
  have hstep1 : |taylorRemainder g G M x₀ y - taylorRemainder g G M x₀ z| / d
      ≤ C * Ig / r ^ 5 + 2 * ‖Q‖ * r := by
    rw [div_le_iff₀ hdpos]
    calc |taylorRemainder g G M x₀ y - taylorRemainder g G M x₀ z|
        ≤ |g' y - g' z|
          + |quadM M x₀ (y - x₀) (y - x₀) - quadM M x₀ (z - x₀) (z - x₀)| := hhd
      _ ≤ C * Ig * d / r ^ 5 + 2 * ‖Q‖ * r * d := by linarith [hgd, hqd]
      _ = (C * Ig / r ^ 5 + 2 * ‖Q‖ * r) * d := by ring
  exact le_trans hstep1 (slope_alg hCpos hωpos hr hInn hIg_le hVval hA1 hA2)

end Submission

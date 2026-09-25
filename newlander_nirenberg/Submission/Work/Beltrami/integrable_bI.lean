import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.norm_cauchyTransform_sub_le

namespace Work.Beltrami

open MeasureTheory Set

noncomputable section

/-- For `x ≥ 0` and any real exponent `α`, `x ^ α * (x ^ 2)⁻¹ ≤ x ^ (α - 2)`: for `x > 0` this
is an equality `x ^ α * x ^ (-2) = x ^ (α - 2)`, while at `x = 0` the left hand side is `0` and
the right hand side is nonnegative.  This is the elementary estimate that makes the Beurling
integrand locally integrable. -/
lemma rpow_mul_inv_sq_le (α : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ α * (x ^ 2)⁻¹ ≤ x ^ (α - 2) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [show ((0 : ℝ) ^ 2)⁻¹ = 0 by norm_num, mul_zero]
    exact Real.rpow_nonneg le_rfl _
  · rw [← Real.rpow_natCast x 2, ← Real.rpow_neg h.le, ← Real.rpow_add h]
    exact le_of_eq (by congr 1)

/-- The Beurling integrand `ζ ↦ (f ζ - χ(ζ-z) f z) (ζ-z)⁻²` (with `χ = bumpC`) is integrable on
`ℂ` when `f` is bounded by `M`, `α`-Hölder with constant `K` (`α > 0`) and supported in the ball
of radius `R`: it is dominated by `K‖ζ-z‖^{α-2}` near `z` (where `χ = 1`) and by `4M` on the
annulus `{1/2 ≤ ‖ζ-z‖ ≤ 1}`, while for `‖ζ-z‖ ≥ 1` it equals `f ζ (ζ-z)⁻²` with `f` supported in
`B(0,R)`. -/
theorem integrable_bI {α K M R : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hM : 0 ≤ M) {f : ℂ → ℂ}
    (hMb : ∀ z, ‖f z‖ ≤ M) (hKb : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → f z = 0) (z : ℂ) :
    MeasureTheory.Integrable
      (fun ζ : ℂ => (f ζ - (Work.Beltrami.bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹)
      MeasureTheory.volume := by
  have hf_cont : Continuous f := Work.CR.Flat.Cauchy.continuous_of_holder hα hK hKb
  -- The integrand, written in the variable `w = ζ - z`.
  set Φ : ℂ → ℂ := fun w => (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ with hΦ
  have hmeasΦ : AEStronglyMeasurable Φ volume := by
    have hbump_cont : Continuous fun w : ℂ => (bumpC w : ℂ) :=
      Complex.continuous_ofReal.comp bumpC_contDiff.continuous
    have h1 : Measurable fun w : ℂ => f (z + w) - (bumpC w : ℂ) * f z :=
      ((hf_cont.comp (continuous_const.add continuous_id)).sub
        (hbump_cont.mul continuous_const)).measurable
    have h2 : Measurable fun w : ℂ => (f (z + w) - (bumpC w : ℂ) * f z) / (w ^ 2) :=
      h1.div (measurable_id.pow_const 2)
    simpa only [hΦ, div_eq_mul_inv] using h2.aestronglyMeasurable
  -- The majorant: the singular term near `0`, a constant on the annulus and a constant on the
  -- support of `f` (which lies in a ball of radius `R + ‖z‖`).
  set G : ℂ → ℝ := fun w =>
      K * ((Metric.ball (0 : ℂ) (1 / 2)).indicator (fun w => ‖w‖ ^ (α - 2)) w)
      + 8 * M * ((Metric.ball (0 : ℂ) 1).indicator (fun _ : ℂ => (1 : ℝ)) w)
      + M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator (fun _ : ℂ => (1 : ℝ)) w)
    with hG
  have hG1 : Integrable (fun w : ℂ =>
      K * ((Metric.ball (0 : ℂ) (1 / 2)).indicator (fun w => ‖w‖ ^ (α - 2)) w)) volume :=
    (IntegrableOn.integrable_indicator
      (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := 1 / 2) (s := α - 2)
        (by linarith))
      Metric.isOpen_ball.measurableSet).const_mul K
  have hG2 : Integrable (fun w : ℂ =>
      8 * M * ((Metric.ball (0 : ℂ) 1).indicator (fun _ : ℂ => (1 : ℝ)) w)) volume :=
    (IntegrableOn.integrable_indicator
      (integrableOn_const (s := Metric.ball (0 : ℂ) 1) (C := (1 : ℝ))
        measure_ball_lt_top.ne (by simp))
      Metric.isOpen_ball.measurableSet).const_mul (8 * M)
  have hG3 : Integrable (fun w : ℂ =>
      M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator (fun _ : ℂ => (1 : ℝ)) w)) volume :=
    (IntegrableOn.integrable_indicator
      (integrableOn_const (s := Metric.ball (0 : ℂ) (R + ‖z‖ + 1)) (C := (1 : ℝ))
        measure_ball_lt_top.ne (by simp))
      Metric.isOpen_ball.measurableSet).const_mul M
  have hGint : Integrable G volume := by
    rw [hG]
    exact (hG1.add hG2).add hG3
  -- The pointwise bound.
  have hbound : ∀ w : ℂ, ‖Φ w‖ ≤ G w := by
    intro w
    have hW : Φ w = (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ := by rw [hΦ]
    rw [hW]
    rcases lt_or_ge ‖w‖ (1 / 2) with h2 | h2
    · -- `‖w‖ < 1/2`: the cutoff equals one, and the Hölder bound gives `K‖w‖^{α-2}`.
      have hbump : bumpC w = 1 := bumpC_eq_one (le_of_lt h2)
      have hmem1 : w ∈ Metric.ball (0 : ℂ) (1 / 2) := by
        rw [Metric.mem_ball, dist_eq_norm]; simpa only [sub_zero] using h2
      have hmem2 : w ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_eq_norm]
        simpa only [sub_zero] using (by linarith : ‖w‖ < 1)
      have hGval : G w = K * ‖w‖ ^ (α - 2) + 8 * M
          + M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator (fun _ : ℂ => (1 : ℝ)) w) := by
        simp only [hG, Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, mul_one]
      rw [hGval]
      have hfw : ‖f (z + w) - f z‖ ≤ K * ‖w‖ ^ α := by
        have h := hKb (z + w) z
        rwa [add_sub_cancel_left] at h
      have hstep : ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
          ≤ K * ‖w‖ ^ α * (‖w‖ ^ 2)⁻¹ := by
        rw [hbump, Complex.ofReal_one, one_mul, norm_mul, norm_inv, norm_pow]
        exact mul_le_mul_of_nonneg_right hfw (inv_nonneg.mpr (by positivity))
      have hind3 : 0 ≤ M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator
          (fun _ : ℂ => (1 : ℝ)) w) :=
        mul_nonneg hM (Set.indicator_nonneg (fun _ _ => by norm_num) w)
      calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
          ≤ K * ‖w‖ ^ α * (‖w‖ ^ 2)⁻¹ := hstep
        _ = K * (‖w‖ ^ α * (‖w‖ ^ 2)⁻¹) := by ring
        _ ≤ K * ‖w‖ ^ (α - 2) :=
            mul_le_mul_of_nonneg_left (rpow_mul_inv_sq_le α (norm_nonneg w)) hK
        _ ≤ K * ‖w‖ ^ (α - 2) + 8 * M
              + M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator
                  (fun _ : ℂ => (1 : ℝ)) w) := by
            linarith [hind3, hM]
    · rcases lt_or_ge ‖w‖ 1 with h1 | h1
      · -- `1/2 ≤ ‖w‖ < 1`: both `f` and the cutoff are bounded, and `‖w‖^{-2} ≤ 4`.
        have hmem2 : w ∈ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm]; simpa only [sub_zero] using h1
        have hnot1 : w ∉ Metric.ball (0 : ℂ) (1 / 2) := by
          rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]
          exact not_lt.mpr h2
        have hGval : G w = 8 * M
            + M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator (fun _ : ℂ => (1 : ℝ)) w) := by
          simp only [hG, Set.indicator_of_notMem hnot1, Set.indicator_of_mem hmem2, mul_one,
            mul_zero, zero_add]
        rw [hGval]
        have hbl : ‖(bumpC w : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpC_nonneg w)]
          exact bumpC_le_one w
        have hinner : ‖f (z + w) - (bumpC w : ℂ) * f z‖ ≤ 2 * M := by
          calc ‖f (z + w) - (bumpC w : ℂ) * f z‖
              ≤ ‖f (z + w)‖ + ‖(bumpC w : ℂ) * f z‖ := norm_sub_le _ _
            _ ≤ M + 1 * M := by
                refine add_le_add (hMb _) ?_
                rw [norm_mul]
                exact mul_le_mul hbl (hMb z) (norm_nonneg _) (by norm_num)
            _ = 2 * M := by ring
        have h4 : (‖w‖ ^ 2)⁻¹ ≤ 4 := by
          have h : ((4 : ℝ)⁻¹) ≤ ‖w‖ ^ 2 := by
            rw [show ((4 : ℝ)⁻¹) = 1 / 4 by norm_num]
            nlinarith [norm_nonneg w, h2]
          exact (inv_le_comm₀ (by positivity : (0:ℝ) < ‖w‖ ^ 2) (by norm_num)).mpr h
        have hind3 : 0 ≤ M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator
            (fun _ : ℂ => (1 : ℝ)) w) :=
          mul_nonneg hM (Set.indicator_nonneg (fun _ _ => by norm_num) w)
        calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
            = ‖f (z + w) - (bumpC w : ℂ) * f z‖ * (‖w‖ ^ 2)⁻¹ := by
              rw [norm_mul, norm_inv, norm_pow]
          _ ≤ 2 * M * 4 :=
              mul_le_mul hinner h4 (inv_nonneg.mpr (by positivity)) (by positivity)
          _ = 8 * M := by ring
          _ ≤ 8 * M + M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator
                (fun _ : ℂ => (1 : ℝ)) w) := by
              linarith [hind3]
      · -- `1 ≤ ‖w‖`: the cutoff vanishes, and `f (z + w)` can be nonzero only for
        -- `‖w‖ ≤ R + ‖z‖`.
        have hbc : bumpC w = 0 := bumpC_eq_zero h1
        have hnot1 : w ∉ Metric.ball (0 : ℂ) (1 / 2) := by
          rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
        have hnot2 : w ∉ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
        have hGval : G w = M * ((Metric.ball (0 : ℂ) (R + ‖z‖ + 1)).indicator
            (fun _ : ℂ => (1 : ℝ)) w) := by
          simp only [hG, Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2,
            mul_zero, add_zero, zero_add]
        rw [hGval]
        by_cases hf0 : f (z + w) = 0
        · simp only [hf0, hbc, Complex.ofReal_zero, zero_mul, sub_zero, norm_zero]
          exact mul_nonneg hM (Set.indicator_nonneg (fun _ _ => by norm_num) w)
        · have hzle : ‖z + w‖ ≤ R := by
            by_contra hc
            exact hf0 (hsupp (z + w) (not_le.mp hc))
          have hmem3 : w ∈ Metric.ball (0 : ℂ) (R + ‖z‖ + 1) := by
            rw [Metric.mem_ball, dist_eq_norm, sub_zero]
            have hle : ‖w‖ ≤ ‖z + w‖ + ‖z‖ := by
              simpa only [add_sub_cancel_left] using norm_sub_le (z + w) z
            linarith
          rw [Set.indicator_of_mem hmem3, mul_one]
          calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
              = ‖f (z + w)‖ * (‖w‖ ^ 2)⁻¹ := by
                rw [hbc, Complex.ofReal_zero, zero_mul, sub_zero, norm_mul, norm_inv, norm_pow]
            _ ≤ M * 1 := by
                refine mul_le_mul (hMb _) ?_ (inv_nonneg.mpr (by positivity)) hM
                exact inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg w])
            _ = M := by ring
  have hΦint : Integrable Φ volume :=
    Integrable.mono' hGint hmeasΦ (Filter.Eventually.of_forall hbound)
  -- Undo the translation `w = ζ - z`.
  have hmp : MeasurePreserving (fun ζ : ℂ => ζ + (-z)) volume volume :=
    measurePreserving_add_right volume (-z)
  have hcomp : Integrable (fun ζ : ℂ => Φ (ζ + (-z))) volume :=
    (hmp.integrable_comp hmeasΦ).mpr hΦint
  refine hcomp.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [hΦ, sub_eq_add_neg]
  rw [show z + (ζ + -z) = ζ by ring]

end

end Work.Beltrami

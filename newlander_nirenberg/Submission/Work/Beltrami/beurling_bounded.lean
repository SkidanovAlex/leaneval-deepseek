import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.norm_cauchyT_le
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.norm_cauchyTransform_sub_le

namespace Work.Beltrami

open MeasureTheory

noncomputable section

/-- For a real number `x ≥ 0` and a real exponent `α`,
`x ^ α * (x ^ 2)⁻¹ = x ^ (α - 2)`. -/
lemma rpow_mul_inv_sq {α : ℝ} (hα : α ≠ 0) (hα2 : α ≠ 2) (x : ℝ) (hx : 0 ≤ x) :
    x ^ α * (x ^ 2)⁻¹ = x ^ (α - 2) := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    rw [Real.zero_rpow (x := α) hα,
      Real.zero_rpow (x := α - 2) (by intro hc; exact hα2 (by linarith))]
    ring
  · rw [← Real.rpow_natCast x 2, ← Real.rpow_neg h.le, ← Real.rpow_add h]
    congr 1

/-- The Beurling transform written as a convolution integral around `z`
(the substitution `ζ = z + w`). -/
lemma beurling_eq_translate (f : ℂ → ℂ) (z : ℂ) :
    beurling f z = (-(Real.pi)⁻¹ : ℝ) •
      ∫ w, (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ := by
  have htrans : (∫ ζ : ℂ, (f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹)
      = ∫ w : ℂ, (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ := by
    rw [← integral_add_right_eq_self
        (fun ζ : ℂ => (f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹) z]
    apply integral_congr_ae
    filter_upwards with w
    rw [show w + z - z = w from by ring, show f (w + z) = f (z + w) from by rw [add_comm]]
  rw [beurling_apply, htrans]

/-- Pointwise bound for the Beurling transform `Work.Beltrami.beurling` of a function that is
bounded by `M`, `α`-Hölder with constant `K` and supported in the ball of radius `R`:
`‖beurling f z‖ ≤ C (M+K) (1+R)` uniformly in `z`.

Suggested route: `beurling f z = -π⁻¹ ∫_ℂ (f (z+w) - bumpC w · f z) / w² dw`; split the plane at
`‖w‖ = 1`: on `‖w‖ ≤ 1` the integrand is dominated by `K ‖w‖^{α-2}` plus `M ‖w‖^{-2}` on the shell
`{1/2 ≤ ‖w‖}`, and outside `‖w‖ > 1` one has `bumpC w = 0`, so only `f` contributes, with
`f (z+w) = 0` unless `‖w‖ ≤ R + ‖z‖` (case split `‖z‖ ≤ 2R+1` / `‖z‖ > 2R+1`).
Useful existing lemmas: `Work.CR.Flat.Cauchy.integral_norm_rpow_ball`,
`Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball`. -/
theorem beurling_bounded {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) (f : ℂ → ℂ)
    (hM : ∀ z, ‖f z‖ ≤ M) (hK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → f z = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, ‖Work.Beltrami.beurling f z‖ ≤ C * (M + K) * (1 + R) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  have hK0 : 0 ≤ K := by
    have h := hK 0 1
    rw [show (0:ℂ) - 1 = -(1:ℂ) from by ring, norm_neg, norm_one, Real.one_rpow, mul_one] at h
    linarith [norm_nonneg (f 0 - f 1)]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hαne2 : α ≠ 2 := by intro hc; rw [hc] at hα1; norm_num at hα1
  refine ⟨2 / α + 10, by positivity, ?_⟩
  intro z
  rw [beurling_eq_translate]
  set F : ℂ → ℂ := fun w => (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ with hF
  set A : Set ℂ := {w : ℂ | 1 ≤ ‖w‖ ∧ ‖z + w‖ < R + 1} with hAset
  let tf : ℂ → ℝ := fun w => K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
  let tg : ℂ → ℝ := fun w => 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
  let th : ℂ → ℝ := fun w => M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w)
  let G : ℂ → ℝ := fun w => tf w + tg w + th w
  change ‖(-(Real.pi)⁻¹ : ℝ) • ∫ w, F w‖ ≤ (2 / α + 10) * (M + K) * (1 + R)
  have hAmeas : MeasurableSet A := by
    rw [hAset]
    exact (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt (continuous_norm.comp (continuous_const.add continuous_id))
        continuous_const).measurableSet
  -- the three majorising pieces
  have ht1 : Integrable tf := by
    have h : Integrable ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2))) :=
      MeasureTheory.IntegrableOn.integrable_indicator
        (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := 1) (s := α - 2) (by linarith))
        Metric.isOpen_ball.measurableSet
    exact h.const_mul K
  have ht2 : Integrable tg := by
    have h : Integrable ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ))) :=
      MeasureTheory.IntegrableOn.integrable_indicator
        (integrableOn_const (s := Metric.ball (0:ℂ) 1) measure_ball_lt_top.ne (by simp))
        Metric.isOpen_ball.measurableSet
    exact h.const_mul (4 * M)
  have ht3 : Integrable th := by
    have hJ : Integrable
        (fun w : ℂ => M * ((Metric.ball (-z) (R + 1)).indicator (fun w => ‖w‖⁻¹) w)) :=
      (integrable_indicator_norm_inv (-z) (R + 1)).const_mul M
    refine MeasureTheory.Integrable.mono' hJ ?_ ?_
    · apply AEMeasurable.aestronglyMeasurable
      apply Measurable.aemeasurable
      exact measurable_const.mul ((continuous_norm.measurable.inv).mul
        (Measurable.indicator measurable_const hAmeas))
    · filter_upwards with w
      have hthw : th w = M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) := rfl
      rw [hthw]
      by_cases hw : w ∈ A
      · have hwb : w ∈ Metric.ball (-z) (R + 1) := by
          rw [hAset] at hw
          rw [Metric.mem_ball, dist_eq_norm]
          rw [show w - -z = w + z from by ring, add_comm]
          exact hw.2
        rw [Set.indicator_of_mem hw, mul_one, Set.indicator_of_mem hwb]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · simp only [Set.indicator_of_notMem hw, mul_zero, norm_zero]
        exact mul_nonneg hM0 (Set.indicator_nonneg (fun a _ => inv_nonneg.mpr (norm_nonneg a)) w)
  have ht12 : Integrable (fun w : ℂ => tf w + tg w) := ht1.add ht2
  have hG_int : Integrable G := (ht1.add ht2).add ht3
  -- pointwise domination
  have hFG : ∀ w : ℂ, ‖F w‖ ≤ G w := by
    intro w
    have hFw : F w = (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ := rfl
    have hGw : G w = K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
        + 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
        + M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) := rfl
    rw [hFw, hGw]
    have hbump_le : ‖(1 : ℂ) - (bumpC w : ℂ)‖ ≤ 1 := by
      have hcast : (1 : ℂ) - (bumpC w : ℂ) = ((1 - bumpC w : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [bumpC_le_one w], by linarith [bumpC_nonneg w]⟩
    rcases lt_or_ge (‖w‖) (1/2) with h2 | h2
    · -- `‖w‖ < 1/2`: the cutoff equals one and the subtraction is exact
      have hbump : bumpC w = 1 := bumpC_eq_one (le_of_lt h2)
      have hmem : w ∈ Metric.ball (0:ℂ) 1 := by
        rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
      have hnotA : w ∉ A := by
        rw [hAset]; intro hc; exact absurd hc.1 (by linarith)
      have hG1 : K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
          + 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
          + M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) = K * ‖w‖ ^ (α - 2) + 4 * M := by
        simp only [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnotA, mul_one, mul_zero,
          add_zero]
      rw [hG1]
      calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
          = ‖(f (z + w) - f z) * (w ^ 2)⁻¹‖ := by
              rw [hbump, Complex.ofReal_one, one_mul]
        _ = ‖f (z + w) - f z‖ * (‖w‖ ^ 2)⁻¹ := by rw [norm_mul, norm_inv, norm_pow]
        _ ≤ K * ‖w‖ ^ α * (‖w‖ ^ 2)⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have h := hK (z + w) z
              rwa [add_sub_cancel_left] at h
        _ = K * ‖w‖ ^ (α - 2) := by
              rw [mul_assoc, rpow_mul_inv_sq hαne hαne2 ‖w‖ (norm_nonneg w)]
        _ ≤ K * ‖w‖ ^ (α - 2) + 4 * M := le_add_of_nonneg_right (by positivity)
    · rcases lt_or_ge (‖w‖) 1 with h1 | h1
      · -- `1/2 ≤ ‖w‖ < 1`: the cutoff is bounded by one
        have hmem : w ∈ Metric.ball (0:ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; exact h1
        have hnotA : w ∉ A := by
          rw [hAset]; intro hc; exact absurd hc.1 (by linarith)
        have hG1 : K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
            + 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
            + M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) = K * ‖w‖ ^ (α - 2) + 4 * M := by
          simp only [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnotA, mul_one, mul_zero,
            add_zero]
        rw [hG1]
        have h4 : (‖w‖ ^ 2)⁻¹ ≤ 4 := by
          rw [inv_le_comm₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
          norm_num
          nlinarith [norm_nonneg w]
        have hinner : ‖f (z + w) - (bumpC w : ℂ) * f z‖ ≤ K * ‖w‖ ^ α + M := by
          have hsub : f (z + w) - (bumpC w : ℂ) * f z
              = (f (z + w) - f z) + ((1 : ℂ) - (bumpC w : ℂ)) * f z := by ring
          rw [hsub]
          refine le_trans (norm_add_le _ _) ?_
          have h3 : ‖f (z + w) - f z‖ ≤ K * ‖w‖ ^ α := by
            have h := hK (z + w) z; rwa [add_sub_cancel_left] at h
          have h5 : ‖((1 : ℂ) - (bumpC w : ℂ)) * f z‖ ≤ 1 * M := by
            rw [norm_mul]
            exact mul_le_mul hbump_le (hM z) (norm_nonneg _) (by norm_num)
          linarith
        calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
            = ‖f (z + w) - (bumpC w : ℂ) * f z‖ * (‖w‖ ^ 2)⁻¹ := by
                rw [norm_mul, norm_inv, norm_pow]
          _ ≤ (K * ‖w‖ ^ α + M) * (‖w‖ ^ 2)⁻¹ :=
                mul_le_mul_of_nonneg_right hinner (by positivity)
          _ = K * ‖w‖ ^ (α - 2) + M * (‖w‖ ^ 2)⁻¹ := by
                rw [add_mul, mul_assoc, rpow_mul_inv_sq hαne hαne2 ‖w‖ (norm_nonneg w)]
          _ ≤ K * ‖w‖ ^ (α - 2) + 4 * M := by
                linarith [mul_le_mul_of_nonneg_left h4 hM0]
      · -- `1 ≤ ‖w‖`: the cutoff vanishes, only the support of `f` contributes
        have hbc : bumpC w = 0 := bumpC_eq_zero h1
        have hnotmem : w ∉ Metric.ball (0:ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
        have hG2 : K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
            + 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
            + M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w)
            = M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) := by
          simp only [Set.indicator_of_notMem hnotmem, mul_zero, add_zero, zero_add]
        rw [hG2]
        by_cases hwA : w ∈ A
        · rw [Set.indicator_of_mem hwA, mul_one]
          have hinv : (‖w‖ ^ 2)⁻¹ ≤ ‖w‖⁻¹ := by
            rw [inv_le_inv₀ (by positivity) (by linarith)]
            nlinarith [norm_nonneg w]
          calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
              = ‖f (z + w) - (bumpC w : ℂ) * f z‖ * (‖w‖ ^ 2)⁻¹ := by
                  rw [norm_mul, norm_inv, norm_pow]
            _ ≤ M * (‖w‖ ^ 2)⁻¹ := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  rw [show f (z + w) - (bumpC w : ℂ) * f z = f (z + w) from by
                    rw [hbc, Complex.ofReal_zero, zero_mul, sub_zero]]
                  exact hM (z + w)
            _ ≤ M * ‖w‖⁻¹ := mul_le_mul_of_nonneg_left hinv hM0
        · rw [Set.indicator_of_notMem hwA, mul_zero, mul_zero]
          have hzR : R < ‖z + w‖ := by
            by_contra hcon
            exact hwA (by rw [hAset]; exact ⟨h1, by linarith [(not_lt.mp hcon)]⟩)
          have hf0 : f (z + w) = 0 := hsupp (z + w) hzR
          simp only [hf0, hbc, Complex.ofReal_zero, zero_mul, sub_zero, norm_zero]
          exact le_refl 0
  -- value of the majorant
  have hG_val : ∫ w : ℂ, G w ≤
      2 * Real.pi * K / α + 4 * Real.pi * M + 6 * Real.pi * M * (1 + R) := by
    have hsplit : ∫ w : ℂ, G w = (∫ w, tf w) + (∫ w, tg w) + (∫ w, th w) := by
      rw [show (∫ w : ℂ, G w) = ∫ w : ℂ, (tf w + tg w + th w) from rfl]
      rw [integral_add ht12 ht3, integral_add ht1 ht2]
    rw [hsplit]
    have hv1 : ∫ w : ℂ, tf w = 2 * Real.pi * K / α := by
      rw [show (∫ w : ℂ, tf w) = ∫ w : ℂ,
        K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w) from rfl]
      rw [integral_const_mul, integral_indicator Metric.isOpen_ball.measurableSet,
        Work.CR.Flat.Cauchy.integral_norm_rpow_ball (ρ := 1) (s := α - 2)
          (by norm_num) (by linarith)]
      rw [Real.one_rpow, show α - 2 + 2 = α from by ring, mul_one, ← mul_div_assoc]
      congr 1
      ring
    have hv2 : ∫ w : ℂ, tg w = 4 * Real.pi * M := by
      rw [show (∫ w : ℂ, tg w) = ∫ w : ℂ,
        4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w) from rfl]
      rw [integral_const_mul, integral_indicator_const (1:ℝ) Metric.isOpen_ball.measurableSet,
        volume_real_ball_one, smul_eq_mul]
      ring
    have hv3 : ∫ w : ℂ, th w ≤ 6 * Real.pi * M * (1 + R) := by
      rw [show (∫ w : ℂ, th w) = ∫ w : ℂ,
        M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) from rfl]
      have hJ : Integrable
          (fun w : ℂ => M * ((Metric.ball (-z) (R + 1)).indicator (fun w => ‖w‖⁻¹) w)) :=
        (integrable_indicator_norm_inv (-z) (R + 1)).const_mul M
      have hle : ∀ w : ℂ, M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w)
          ≤ M * ((Metric.ball (-z) (R + 1)).indicator (fun w => ‖w‖⁻¹) w) := by
        intro w
        by_cases hw : w ∈ A
        · have hwb : w ∈ Metric.ball (-z) (R + 1) := by
            rw [hAset] at hw
            rw [Metric.mem_ball, dist_eq_norm]
            rw [show w - -z = w + z from by ring, add_comm]
            exact hw.2
          rw [Set.indicator_of_mem hw, mul_one, Set.indicator_of_mem hwb]
        · rw [Set.indicator_of_notMem hw, mul_zero, mul_zero]
          exact mul_nonneg hM0 (Set.indicator_nonneg (fun a _ => inv_nonneg.mpr (norm_nonneg a)) w)
      have hmono := integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun w : ℂ => mul_nonneg hM0
          (mul_nonneg (inv_nonneg.mpr (norm_nonneg w))
            (Set.indicator_nonneg (fun a _ => by norm_num) w))))
        hJ (Filter.Eventually.of_forall hle)
      have hJ2 : ∫ (a : ℂ), M * (Metric.ball (-z) (R + 1)).indicator (fun w => ‖w‖⁻¹) a
          = M * ∫ a in Metric.ball (-z) (R + 1), ‖a‖⁻¹ := by
        rw [integral_const_mul, integral_indicator Metric.isOpen_ball.measurableSet]
      rw [hJ2] at hmono
      have hb := integral_ball_norm_inv_le (-z) (R + 1) (by linarith)
      have hbound : M * (∫ w in Metric.ball (-z) (R + 1), ‖w‖⁻¹)
          ≤ 6 * Real.pi * M * (1 + R) := by
        have h4 : (1 + (R + 1)) ≤ 2 * (1 + R) := by linarith
        calc M * (∫ w in Metric.ball (-z) (R + 1), ‖w‖⁻¹)
            ≤ M * (3 * Real.pi * (1 + (R + 1))) := mul_le_mul_of_nonneg_left hb hM0
          _ ≤ M * (3 * Real.pi * (2 * (1 + R))) := by
                refine mul_le_mul_of_nonneg_left ?_ hM0
                nlinarith [Real.pi_pos, h4]
          _ = 6 * Real.pi * M * (1 + R) := by ring
      linarith [hmono, hbound]
    linarith [hv1, hv2, hv3]
  have hmain : ‖∫ w, F w‖ ≤ ∫ w : ℂ, G w := by
    refine le_trans (norm_integral_le_integral_norm F) ?_
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _) hG_int
      (Filter.Eventually.of_forall hFG)
  have hnorm : ‖(-(Real.pi)⁻¹ : ℝ) • ∫ w, F w‖ = Real.pi⁻¹ * ‖∫ w, F w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
  have harith : Real.pi⁻¹ * (2 * Real.pi * K / α + 4 * Real.pi * M + 6 * Real.pi * M * (1 + R))
      = 2 * K / α + 4 * M + 6 * M * (1 + R) := by
    field_simp
  calc ‖(-(Real.pi)⁻¹ : ℝ) • ∫ w, F w‖
      = Real.pi⁻¹ * ‖∫ w, F w‖ := hnorm
    _ ≤ Real.pi⁻¹ * ∫ w : ℂ, G w := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ ≤ Real.pi⁻¹ * (2 * Real.pi * K / α + 4 * Real.pi * M + 6 * Real.pi * M * (1 + R)) :=
        mul_le_mul_of_nonneg_left hG_val (by positivity)
    _ = 2 * K / α + 4 * M + 6 * M * (1 + R) := harith
    _ ≤ (2 / α + 10) * (M + K) * (1 + R) := by
        have hαinv : (0:ℝ) < 2/α := by positivity
        have h1R : (1:ℝ) ≤ 1 + R := by linarith
        have h2Ka : 2 * K / α = (2/α) * K := by ring
        rw [h2Ka]
        nlinarith [hM0, hK0, hR, hαinv, h1R, mul_nonneg hM0 hK0, mul_nonneg hM0 hR,
          mul_nonneg hK0 hR, mul_nonneg hαinv.le hM0, mul_nonneg hαinv.le hK0,
          mul_nonneg (mul_nonneg hM0 hK0) hR]

end

end Work.Beltrami

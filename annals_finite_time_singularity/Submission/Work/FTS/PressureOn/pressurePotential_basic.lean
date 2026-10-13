/-
# `Work.FTS.PressureOn.pressurePotential_basic`

Regularity, boundedness and decay of the Newtonian potential of the Lamb vector,

  `pressurePotential f x = -∫ y, ⟪nablaNfund (x - y), f y⟫ dy`,

for `f : ℝ³ → ℝ³` continuous with compact support.  The kernel is
`nablaNfund z = (4π‖z‖³)⁻¹ • z`, so `‖nablaNfund z‖ = (4π)⁻¹‖z‖⁻²`: singular of
Riesz type `-2` in dimension `3`, i.e. *absolutely* integrable at the origin
(`∫_{B(0,1)} ‖z‖⁻² dz = 4π < ∞`) and decaying at infinity.  Consequently:

* `pressurePotential f` is continuous — dominated convergence in the shifted
  form `q x = ∫ z, ⟪∇N z, f (x - z)⟫`, whose integrand is dominated for `x`
  near `x₀` by `C ‖z‖⁻² 1_{closedBall 0 (R+‖x₀‖+1)}`, an integrable function
  because `f` is supported in `closedBall 0 R`;
* it is bounded: on the compact ball `closedBall 0 (2R)` by continuity, and
  outside it by the kernel decay `‖x - y‖ ≥ ‖x‖/2`;
* it tends to `0` at infinity (`Filter.cocompact`), with the explicit rate
  `|pressurePotential f x| ≤ C ‖x‖⁻²`.

The self-contained model estimate `modelDecayBound_aux` (the `L²`-marginal
kernel bound `(‖x - y‖²)⁻¹ ≤ 4‖x‖⁻²` on `ball 0 R` for `‖x‖ > 2R`) is proved
here; a sibling development of the same estimate lives in
`Submission/Work/FTS/PressureOn/modelDecayBound.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Bornology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## Pointwise bounds for the kernel -/

private lemma inv_pow_three_mul_le (a : ℝ) (ha : 0 ≤ a) : (a ^ 3)⁻¹ * a ≤ (a ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]; norm_num
  · refine le_of_eq ?_
    field_simp

/-- The pointwise size of the gradient of the fundamental solution:
`‖nablaNfund z‖ ≤ (4π)⁻¹ ‖z‖⁻²` (with the junk value `0` at `z = 0`, where the
inequality is also true). -/
private lemma norm_nablaNfund_le (z : R3) : ‖nablaNfund z‖ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  have h : ‖nablaNfund z‖ = ‖newtonGrad z‖ := by
    rw [nablaNfund_eq_neg_newtonGrad, norm_neg]
  rw [h, norm_newtonGrad]
  have h2 : (‖z‖ ^ 3)⁻¹ * ‖z‖ ≤ (‖z‖ ^ 2)⁻¹ := inv_pow_three_mul_le ‖z‖ (norm_nonneg z)
  calc (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ * ‖z‖
      = (4 * Real.pi)⁻¹ * ((‖z‖ ^ 3)⁻¹ * ‖z‖) := by ring
    _ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The kernel is Borel measurable (its only discontinuity is at the origin,
where it is declared to be `0`). -/
private lemma meas_nablaNfund : Measurable (fun z : R3 => nablaNfund z) := by
  unfold nablaNfund
  have h1 : Measurable (fun z : R3 => (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹) := by fun_prop
  have h2 : Measurable (fun z : R3 => z) := measurable_id
  exact h1.smul h2

/-- A.e. strong measurability of the integrand of the potential in the shifted
form `z ↦ ⟪∇N z, f (x - z)⟫`. -/
private lemma aeStronglyMeasurable_shifted (f : R3 → R3) (hf : Continuous f) (x : R3) :
    AEStronglyMeasurable (fun z : R3 => inner ℝ (nablaNfund z) (f (x - z))) volume := by
  have hm1 : Measurable (fun z : R3 => nablaNfund z) := meas_nablaNfund
  have hm2 : Measurable (fun z : R3 => f (x - z)) :=
    hf.measurable.comp (continuous_const.sub continuous_id).measurable
  exact (Measurable.inner hm1 hm2).aestronglyMeasurable

/-- A.e. strong measurability of the integrand of the potential in its defining
(unshifted) form `y ↦ ⟪∇N (x - y), f y⟫`. -/
private lemma aeStronglyMeasurable_unshifted (f : R3 → R3) (hf : Continuous f) (x : R3) :
    AEStronglyMeasurable (fun y : R3 => inner ℝ (nablaNfund (x - y)) (f y)) volume := by
  have hm1 : Measurable (fun y : R3 => nablaNfund (x - y)) :=
    meas_nablaNfund.comp (continuous_const.sub continuous_id).measurable
  have hm2 : Measurable (fun y : R3 => f y) := hf.measurable
  exact (Measurable.inner hm1 hm2).aestronglyMeasurable

/-! ## Bounded data: a sup bound and a supporting ball -/

private lemma exists_bound_support {f : R3 → R3} (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 < R ∧ (∀ y, ‖f y‖ ≤ M) ∧ (∀ y, R ≤ ‖y‖ → f y = 0) := by
  obtain ⟨M₀, hM₀⟩ := hf.bounded_above_of_compact_support hcs
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hcs.isBounded.exists_pos_norm_le
  refine ⟨max M₀ 0, R₀ + 1, le_max_right _ _, by linarith, fun y => ?_, fun y hy => ?_⟩
  · exact le_trans (hM₀ y) (le_max_left _ _)
  · by_contra h
    have hy1 : y ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr h)
    have hy2 := hR₀ y hy1
    linarith

/-- Pointwise domination of the integrand of the potential by the model function
`(4π)⁻¹ M (‖x - y‖²)⁻¹ 1_{ball 0 R} y`, where `M` bounds `‖f‖` and `f` vanishes
outside the ball of radius `R`. -/
private lemma integrand_le {f : R3 → R3} {M R : ℝ} (hbd : ∀ y, ‖f y‖ ≤ M)
    (hsupp : ∀ y, R ≤ ‖y‖ → f y = 0) (x y : R3) :
    ‖inner ℝ (nablaNfund (x - y)) (f y)‖
      ≤ (4 * Real.pi)⁻¹ * M *
          ((‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) := by
  by_cases hy : y ∈ Metric.ball (0 : R3) R
  · rw [Set.indicator_of_mem hy, mul_one]
    calc ‖inner ℝ (nablaNfund (x - y)) (f y)‖
        ≤ ‖nablaNfund (x - y)‖ * ‖f y‖ := norm_inner_le_norm _ _
      _ ≤ ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹) * M :=
          mul_le_mul (norm_nablaNfund_le _) (hbd y) (norm_nonneg _) (by positivity)
      _ = (4 * Real.pi)⁻¹ * M * (‖x - y‖ ^ 2)⁻¹ := by ring
  · rw [Set.indicator_of_notMem hy, mul_zero, mul_zero]
    have hy2 : R ≤ ‖y‖ := by
      rw [Metric.mem_ball, not_lt, dist_eq_norm, sub_zero] at hy; exact hy
    rw [hsupp y hy2]
    simp

/-! ## The shifted form of the potential -/

/-- The change of variables `z = x - y` in the defining integral: the potential
is the convolution of the kernel with `f`, read at `x`. -/
private lemma pressurePotential_eq_shifted (f : R3 → R3) (x : R3) :
    pressurePotential f x = -∫ z, inner ℝ (nablaNfund z) (f (x - z)) := by
  set H : R3 → ℝ := fun z => inner ℝ (nablaNfund z) (f (x - z)) with hH
  have h1 : (fun y => inner ℝ (nablaNfund (x - y)) (f y)) = fun y => H (-(y - x)) := by
    funext y; simp [hH, neg_sub]
  rw [pressurePotential_apply, h1, MeasureTheory.integral_sub_right_eq_self (fun w => H (-w)) x,
    MeasureTheory.integral_neg_eq_self H volume]

/-! ## Continuity -/

/-- Integrability of the singular majorant `‖z‖⁻²` on a ball centred at the
origin (the `L²`-marginal kernel is absolutely integrable at the origin in
dimension `3`). -/
private lemma integrable_kernel_ball_closed (S : ℝ) :
    Integrable (fun z : R3 =>
      (‖z‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) z) volume := by
  have h0 : ∀ T : ℝ, IntegrableOn (fun z : R3 => (‖z‖ ^ 2)⁻¹) (Metric.ball (0 : R3) T) := by
    intro T
    refine (MeasureTheory.integrableOn_fun_norm_addHaar (μ := volume)
      (f := fun y : ℝ => (y ^ 2)⁻¹) (r := T)).mpr ?_
    have h3 : Module.finrank ℝ R3 = 3 := by rw [finrank_euclideanSpace_fin]
    rw [h3]
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (1 : ℝ))
      (integrableOn_const (C := (1 : ℝ)) (measure_Ioo_lt_top.ne)) ?_ measurableSet_Ioo
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    simp only [smul_eq_mul]
    rw [show (3 : ℕ) - 1 = 2 from rfl]
    exact (mul_inv_cancel₀ (pow_ne_zero 2 hy0)).symm
  have hclosed : IntegrableOn (fun z : R3 => (‖z‖ ^ 2)⁻¹) (Metric.closedBall (0 : R3) S) := by
    refine (h0 (max S 0 + 1)).mono_set (fun z hz => ?_)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith [le_max_left S 0]
  have hInd : Integrable ((Metric.closedBall (0 : R3) S).indicator
      (fun z : R3 => (‖z‖ ^ 2)⁻¹)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr hclosed
  refine hInd.congr ?_
  filter_upwards with z
  by_cases hz : z ∈ Metric.closedBall (0 : R3) S
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

/-- At every point `x₀`, the shifted singular integral is continuous: dominated
convergence for `x` near `x₀`, dominated by the integrable function
`(4π)⁻¹ M ‖z‖⁻² 1_{closedBall 0 (R + ‖x₀‖ + 1)}`. -/
private lemma continuousAt_shifted (f : R3 → R3) (hf : Continuous f)
    (hcs : HasCompactSupport f) (x₀ : R3) :
    ContinuousAt (fun x : R3 => ∫ z, inner ℝ (nablaNfund z) (f (x - z))) x₀ := by
  obtain ⟨M, R, hM, hR, hbd, hsupp⟩ := exists_bound_support hf hcs
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 x₀)
    (fun z : R3 => (4 * Real.pi)⁻¹ * M * ((‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z)) ?_ ?_
    ((integrable_kernel_ball_closed (R + ‖x₀‖ + 1)).const_mul ((4 * Real.pi)⁻¹ * M)) ?_
  · filter_upwards with x
    exact aeStronglyMeasurable_shifted f hf x
  · filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
    refine Eventually.of_forall fun z => ?_
    by_cases hz : f (x - z) = 0
    · rw [hz, inner_zero_right, norm_zero]
      have hind : 0 ≤ (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator
          (fun _ => (1 : ℝ)) z := Set.indicator_nonneg (fun _ _ => zero_le_one) z
      exact mul_nonneg (mul_nonneg (by positivity) hM) (mul_nonneg (by positivity) hind)
    · have hzR : ‖x - z‖ < R := by
        by_contra h
        exact hz (hsupp (x - z) (not_lt.mp h))
      have hx1 : ‖x‖ ≤ ‖x₀‖ + 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hx
        have h2 : ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
        rw [h2]
        linarith [norm_add_le (x - x₀) x₀]
      have hzx : ‖z‖ ≤ R + ‖x₀‖ + 1 := by
        have h2 : ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        rw [h2]
        have h3 : ‖z - x‖ = ‖x - z‖ := norm_sub_rev z x
        linarith [norm_add_le (z - x) x]
      have hzball : z ∈ Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1) := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hzx
      rw [Set.indicator_of_mem hzball, mul_one]
      calc ‖inner ℝ (nablaNfund z) (f (x - z))‖
          ≤ ‖nablaNfund z‖ * ‖f (x - z)‖ := norm_inner_le_norm _ _
        _ ≤ ((4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) * M :=
            mul_le_mul (norm_nablaNfund_le z) (hbd _) (norm_nonneg _) (by positivity)
        _ = (4 * Real.pi)⁻¹ * M * (‖z‖ ^ 2)⁻¹ := by ring
  · filter_upwards with z
    exact (continuous_const.inner (hf.comp (continuous_id.sub continuous_const))).continuousAt

/-- **The potential is continuous**. -/
private lemma pressurePotential_continuous {f : R3 → R3} (hf : Continuous f)
    (hcs : HasCompactSupport f) : Continuous (pressurePotential f) := by
  have hfun : pressurePotential f = fun x => -∫ z, inner ℝ (nablaNfund z) (f (x - z)) := by
    funext x; exact pressurePotential_eq_shifted f x
  rw [hfun, continuous_iff_continuousAt]
  intro x₀
  exact (continuousAt_shifted f hf hcs x₀).neg

/-! ## The model decay estimate for the kernel -/

/-- **The `L²`-marginal kernel bound.**  For `‖x‖ > 2R` and `y ∈ ball 0 R`,
`‖x - y‖ ≥ ‖x‖ - ‖y‖ ≥ ‖x‖/2`, so `(‖x - y‖²)⁻¹ ≤ 4‖x‖⁻²`; integrating over the
ball gives `∫ (‖x - y‖²)⁻¹ 1_{ball 0 R}(y) ≤ 4‖x‖⁻² vol (ball 0 R)`. -/
private lemma modelDecayBound_aux (R : ℝ) (hR : 0 ≤ R) (x : R3) (hx : 2 * R < ‖x‖) :
    Integrable (fun y : R3 => (‖x - y‖ ^ 2)⁻¹ *
        (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) volume
      ∧ (∫ y, (‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y)
          ≤ 4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal := by
  have hxpos : 0 < ‖x‖ := by linarith
  have hxhalf : 0 < ‖x‖ / 2 := by linarith
  have hmeasBall : MeasurableSet (Metric.ball (0 : R3) R) := measurableSet_ball
  have hvolne : volume (Metric.ball (0 : R3) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : R3) R).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  -- on the closed ball the kernel is bounded below by `‖x‖/2`
  have hge : ∀ y ∈ Metric.closedBall (0 : R3) R, ‖x‖ / 2 ≤ ‖x - y‖ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      have h2 : ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      rw [h2]; exact norm_add_le _ _
    linarith
  -- the kernel is continuous on the closed ball, where it never vanishes
  have hcont : ContinuousOn (fun y : R3 => (‖x - y‖ ^ 2)⁻¹) (Metric.closedBall (0 : R3) R) := by
    refine ContinuousOn.inv₀ ((continuous_const.sub continuous_id).norm.pow 2).continuousOn ?_
    intro y hy
    refine pow_ne_zero 2 (ne_of_gt ?_)
    exact lt_of_lt_of_le hxhalf (hge y hy)
  have hIntCB : IntegrableOn (fun y : R3 => (‖x - y‖ ^ 2)⁻¹) (Metric.closedBall (0 : R3) R) :=
    hcont.integrableOn_compact (isCompact_closedBall (0 : R3) R)
  have hIntA : IntegrableOn (fun y : R3 => (‖x - y‖ ^ 2)⁻¹) (Metric.ball (0 : R3) R) :=
    hIntCB.mono_set Metric.ball_subset_closedBall
  have hIndA : Integrable ((Metric.ball (0 : R3) R).indicator
      (fun y : R3 => (‖x - y‖ ^ 2)⁻¹)) volume :=
    (integrable_indicator_iff hmeasBall).mpr hIntA
  have heq : ∀ y : R3, (‖x - y‖ ^ 2)⁻¹ *
        (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y
      = (Metric.ball (0 : R3) R).indicator (fun y : R3 => (‖x - y‖ ^ 2)⁻¹) y := by
    intro y
    by_cases hy : y ∈ Metric.ball (0 : R3) R
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hIntModel : Integrable (fun y : R3 => (‖x - y‖ ^ 2)⁻¹ *
      (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) volume := by
    refine hIndA.congr ?_
    filter_upwards with y
    exact (heq y).symm
  constructor
  · exact hIntModel
  · -- the pointwise bound on the ball
    have hpt : ∀ y : R3, (‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator
          (fun _ => (1 : ℝ)) y
        ≤ 4 * (‖x‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ Metric.ball (0 : R3) R
      · rw [Set.indicator_of_mem hy, mul_one, mul_one]
        have h1 : ‖x‖ / 2 ≤ ‖x - y‖ := hge y (Metric.ball_subset_closedBall hy)
        have h2 : (‖x‖ / 2) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hxhalf h1
        have h3 : (‖x - y‖ ^ 2)⁻¹ ≤ ((‖x‖ / 2) ^ 2)⁻¹ :=
          (inv_le_inv₀ (pow_pos hpos 2) (pow_pos hxhalf 2)).mpr h2
        have h4 : ((‖x‖ / 2) ^ 2)⁻¹ = 4 * (‖x‖ ^ 2)⁻¹ := by
          field_simp
          ring
        linarith [h3, h4]
      · rw [Set.indicator_of_notMem hy, mul_zero, mul_zero]
    have hConstInt : Integrable (fun y : R3 => 4 * (‖x‖ ^ 2)⁻¹ *
        (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) volume := by
      have heqc : (fun y : R3 => 4 * (‖x‖ ^ 2)⁻¹ *
            (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y)
          = (Metric.ball (0 : R3) R).indicator (fun _ => 4 * (‖x‖ ^ 2)⁻¹) := by
        funext y
        by_cases hy : y ∈ Metric.ball (0 : R3) R
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
      rw [heqc]
      exact (integrable_indicator_iff hmeasBall).mpr
        (integrableOn_const (C := 4 * (‖x‖ ^ 2)⁻¹) hvolne)
    calc ∫ y, (‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y
        ≤ ∫ y, 4 * (‖x‖ ^ 2)⁻¹ *
            (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y :=
          integral_mono hIntModel hConstInt hpt
      _ = 4 * (‖x‖ ^ 2)⁻¹ *
            ∫ y, (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y :=
          integral_const_mul _ _
      _ = 4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal := by
          rw [integral_indicator hmeasBall, setIntegral_const, Measure.real_def]
          simp only [smul_eq_mul, mul_one]

/-! ## Decay at infinity -/

/-- For `‖x‖ > 2R` the kernel factor is `≤ 4‖x‖⁻²` on the support of `f`, which
gives the quantitative decay of the potential. -/
private lemma pressurePotential_decay {f : R3 → R3} (hf : Continuous f) {M R : ℝ} (hM : 0 ≤ M)
    (hR : 0 ≤ R) (hbd : ∀ y, ‖f y‖ ≤ M) (hsupp : ∀ y, R ≤ ‖y‖ → f y = 0) {x : R3}
    (hx : 2 * R < ‖x‖) :
    |pressurePotential f x| ≤ (4 * Real.pi)⁻¹ * M *
      (4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal) := by
  obtain ⟨hInt, hBnd⟩ := modelDecayBound_aux R hR x hx
  have hIntL : Integrable (fun y : R3 => ‖inner ℝ (nablaNfund (x - y)) (f y)‖) volume := by
    refine Integrable.mono' (g := fun y : R3 => (4 * Real.pi)⁻¹ * M *
      ((‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y)) ?_ ?_ ?_
    · exact hInt.const_mul _
    · exact (aeStronglyMeasurable_unshifted f hf x).norm
    · filter_upwards with y
      simpa only [Real.norm_eq_abs, abs_abs] using integrand_le hbd hsupp x y
  calc |pressurePotential f x| = |∫ y, inner ℝ (nablaNfund (x - y)) (f y)| := by
        rw [pressurePotential_apply, abs_neg]
    _ ≤ ∫ y, ‖inner ℝ (nablaNfund (x - y)) (f y)‖ := abs_integral_le_integral_abs
    _ ≤ ∫ y, (4 * Real.pi)⁻¹ * M *
          ((‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) :=
        integral_mono hIntL (hInt.const_mul _) (fun y => integrand_le hbd hsupp x y)
    _ = (4 * Real.pi)⁻¹ * M * ∫ y,
          ((‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) :=
        integral_const_mul _ _
    _ ≤ (4 * Real.pi)⁻¹ * M *
          (4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal) :=
        mul_le_mul_of_nonneg_left hBnd (by positivity)

/-- `‖x‖⁻² → 0` along the cocompact filter of `ℝ³`. -/
private lemma tendsto_normSq_inv_cocompact :
    Filter.Tendsto (fun x : R3 => (‖x‖ ^ 2)⁻¹) (Filter.cocompact R3) (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := Filter.Tendsto.inv_tendsto_atTop tendsto_id
  have h2 : Tendsto (fun t : ℝ => (t⁻¹) ^ 2) atTop (nhds 0) := by
    simpa using h1.pow 2
  have h3 : Tendsto (fun t : ℝ => (t ^ 2)⁻¹) atTop (nhds 0) := by
    simpa only [inv_pow] using h2
  exact h3.comp tendsto_norm_cocompact_atTop

/-- **The potential vanishes at infinity**, at the rate `‖x‖⁻²`. -/
private lemma pressurePotential_tendsto_zero {f : R3 → R3} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    Filter.Tendsto (pressurePotential f) (Filter.cocompact R3) (nhds 0) := by
  obtain ⟨M, R, hM, hR, hbd, hsupp⟩ := exists_bound_support hf hcs
  have hR0 : 0 ≤ R := le_of_lt hR
  have hev : ∀ᶠ x in Filter.cocompact R3, 2 * R < ‖x‖ :=
    (tendsto_norm_cocompact_atTop (E := R3)).eventually (eventually_gt_atTop (2 * R))
  have hbound : ∀ᶠ x in Filter.cocompact R3,
      |pressurePotential f x|
        ≤ ((4 * Real.pi)⁻¹ * M * (4 * (volume (Metric.ball (0 : R3) R)).toReal))
            * (‖x‖ ^ 2)⁻¹ := by
    filter_upwards [hev] with x hx
    have h := pressurePotential_decay hf hM hR0 hbd hsupp hx
    calc |pressurePotential f x| ≤ (4 * Real.pi)⁻¹ * M *
          (4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal) := h
      _ = ((4 * Real.pi)⁻¹ * M * (4 * (volume (Metric.ball (0 : R3) R)).toReal))
            * (‖x‖ ^ 2)⁻¹ := by ring
  refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
  refine squeeze_zero' ?_ hbound ?_
  · filter_upwards with x; exact abs_nonneg _
  · simpa using tendsto_normSq_inv_cocompact.const_mul _

/-- **The potential is bounded**: by continuity on the compact ball
`closedBall 0 (2R)`, and by the decay estimate outside it. -/
private lemma pressurePotential_bounded {f : R3 → R3} (hf : Continuous f)
    (hcs : HasCompactSupport f) : ∃ C, ∀ x, |pressurePotential f x| ≤ C := by
  obtain ⟨M, R, hM, hR, hbd, hsupp⟩ := exists_bound_support hf hcs
  have hR0 : 0 ≤ R := le_of_lt hR
  have hcont : Continuous (pressurePotential f) := pressurePotential_continuous hf hcs
  obtain ⟨C₁, hC₁⟩ :=
    (isCompact_closedBall (0 : R3) (2 * R)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C₁ ((4 * Real.pi)⁻¹ * M *
      (4 * (2 * R)⁻¹ ^ 2 * (volume (Metric.ball (0 : R3) R)).toReal)), fun x => ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : R3) (2 * R)
  · have h := hC₁ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · have hx' : 2 * R < ‖x‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
      exact not_le.mp hx
    have h := pressurePotential_decay hf hM hR0 hbd hsupp hx'
    have h2 : (‖x‖ ^ 2)⁻¹ ≤ (2 * R)⁻¹ ^ 2 := by
      have h4 : 0 < 2 * R := by linarith
      have h5 : 2 * R ≤ ‖x‖ := le_of_lt hx'
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ h4 h5) 2
    calc |pressurePotential f x| ≤ (4 * Real.pi)⁻¹ * M *
          (4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal) := h
      _ ≤ (4 * Real.pi)⁻¹ * M *
          (4 * ((2 * R)⁻¹ ^ 2) * (volume (Metric.ball (0 : R3) R)).toReal) := by
          gcongr
      _ ≤ max C₁ ((4 * Real.pi)⁻¹ * M *
          (4 * (2 * R)⁻¹ ^ 2 * (volume (Metric.ball (0 : R3) R)).toReal)) := le_max_right _ _

/-! ## The statement -/

theorem pressurePotential_basic {f : R3 → R3} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (pressurePotential f) ∧ (∃ C, ∀ x, |pressurePotential f x| ≤ C) ∧
      Filter.Tendsto (pressurePotential f) (Filter.cocompact R3) (nhds 0) :=
  ⟨pressurePotential_continuous hf hcs, pressurePotential_bounded hf hcs,
    pressurePotential_tendsto_zero hf hcs⟩

end Work.FTS.PressureOn

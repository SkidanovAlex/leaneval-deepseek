import Mathlib
import Submission.Work.Repel.Koebe.Setup

/-!
# The `∂̄`-integral of the winding number of an exterior map

For `g` holomorphic on the exterior `{1 < ‖z‖}` of the unit disc, `r > 1` and `G` of class `C¹`
with compact support,

`∫ ζ, wind g r ζ * ∂̄G ζ = -i ∮_{|z| = r} G (g z) · g'(z) dz`.

This is the "change of variables" (or Stokes) identity behind Grönwall's area theorem: the winding
number function of the curve `z ↦ g z` is the Cauchy transform of the push-forward of `dz`, hence
its `∂̄`-derivative is (a multiple of) the push-forward measure of the curve.  The proof is Fubini
together with the Cauchy–Pompeiu representation formula `dbar_representation`:
`∫ ζ, ∂̄G ζ / (w - ζ) = 2π G w` for every `w`.

## Contents

* `integral_inv_norm_ball`: `∫_{‖η‖ < 1} ‖η‖⁻¹ = 2π` (the two-dimensional integrability of the
  Cauchy kernel), obtained from the polar-coordinate formula `integral_fun_norm_addHaar`;
* `continuousOn_deriv_circle`: `θ ↦ deriv g (circleMap 0 r θ)` and `θ ↦ g (circleMap 0 r θ)` are
  continuous on `[0, 2π]` when `r > 1`;
* `kernel_uniform_bound`: `∫ ζ, ‖D ζ‖ ‖w - ζ‖⁻¹` is bounded uniformly in `w` for continuous
  compactly supported `D` (the locally integrable Cauchy kernel);
* `integrable_curve_kernel`: the joint integrand of Fubini is integrable;
* `integrable_inv_sub_mul`, `integral_sub_inv_mul_dbar`: the Cauchy–Pompeiu identity in the form
  used below;
* `dbar_wind_integral`: the theorem.
-/

open MeasureTheory Filter Topology
open scoped Topology

noncomputable section

namespace Work.Repel.Koebe

lemma vol_real_ball_one : (volume.real (Metric.ball (0 : ℂ) 1)) = Real.pi := by
  rw [Measure.real_def, Complex.volume_ball]
  norm_num

/-- The two-dimensional integrability of the Cauchy kernel:
`∫_{‖η‖ < 1} ‖η‖⁻¹ = 2π`. -/
lemma integral_inv_norm_ball :
    ∫ η in Metric.ball (0 : ℂ) 1, (‖η‖)⁻¹ = 2 * Real.pi := by
  have hpt : ∀ η : ℂ, (Metric.ball (0 : ℂ) 1).indicator (fun η : ℂ => (‖η‖)⁻¹) η
      = (fun y : ℝ => if y < 1 then y⁻¹ else 0) ‖η‖ := by
    intro η
    by_cases h : η ∈ Metric.ball (0 : ℂ) 1
    · have h' : ‖η‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using h
      rw [Set.indicator_of_mem h]
      simp only [h', if_true]
    · have h' : ¬ ‖η‖ < 1 := fun hc => h (by simpa [Metric.mem_ball, dist_zero_right] using hc)
      rw [Set.indicator_of_notMem h]
      simp only [h', if_false]
  have hinner : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (if y < 1 then y⁻¹ else 0) = 1 := by
    have hcongr : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
        (if y < 1 then y⁻¹ else 0) = (Set.Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y := by
      intro y hy
      rw [Complex.finrank_real_complex]
      norm_num
      by_cases hy1 : y < 1
      · have hmem : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy, hy1⟩
        rw [if_pos hy1, Set.indicator_of_mem hmem]
        exact mul_inv_cancel₀ (ne_of_gt hy)
      · have hmem : y ∉ Set.Ioo (0 : ℝ) 1 := fun hc => hy1 hc.2
        rw [if_neg hy1, Set.indicator_of_notMem hmem]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      ← MeasureTheory.integral_indicator measurableSet_Ioi, Set.indicator_indicator]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 := by
      ext y; constructor <;> intro h
      · exact h.2
      · exact ⟨h.1, h⟩
    rw [hset, MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Ioo]
    simp [Measure.real_def, Real.volume_Ioo]
  rw [← MeasureTheory.integral_indicator measurableSet_ball]
  calc ∫ η, (Metric.ball (0 : ℂ) 1).indicator (fun η => (‖η‖)⁻¹) η
      = ∫ η, (fun y : ℝ => if y < 1 then y⁻¹ else 0) (‖η‖) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = Module.finrank ℝ ℂ • (volume.real (Metric.ball (0 : ℂ) 1)) •
          ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • (if y < 1 then y⁻¹ else 0) :=
        MeasureTheory.integral_fun_norm_addHaar (E := ℂ) (F := ℝ) volume
          (fun y : ℝ => if y < 1 then y⁻¹ else 0)
    _ = 2 * Real.pi := by
        rw [hinner, vol_real_ball_one, Complex.finrank_real_complex]
        norm_num

/-- Continuity of `deriv g` and `g` along the circle `‖z‖ = r` when `r > 1`. -/
theorem continuousOn_deriv_circle (g : ℂ → ℂ) (r : ℝ) (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z) :
    ContinuousOn (fun θ : ℝ => deriv g (circleMap 0 r θ)) (Set.uIcc 0 (2 * Real.pi)) ∧
      ContinuousOn (fun θ : ℝ => g (circleMap 0 r θ)) (Set.uIcc 0 (2 * Real.pi)) := by
  have hnorm : ∀ θ : ℝ, 1 < ‖circleMap 0 r θ‖ := by
    intro θ
    rw [norm_circleMap_zero, abs_of_pos (lt_trans zero_lt_one hr)]
    exact hr
  constructor
  · intro θ _
    have hca : ContinuousAt (fun θ : ℝ => deriv g (circleMap 0 r θ)) θ :=
      ContinuousAt.comp ((hg _ (hnorm θ)).deriv.continuousAt)
        (continuous_circleMap 0 r).continuousAt
    exact hca.continuousWithinAt
  · intro θ _
    have hca : ContinuousAt (fun θ : ℝ => g (circleMap 0 r θ)) θ :=
      ContinuousAt.comp ((hg _ (hnorm θ)).continuousAt) (continuous_circleMap 0 r).continuousAt
    exact hca.continuousWithinAt

/-- The Cauchy kernel is integrable against a continuous compactly supported function. -/
lemma integrable_inv_sub_mul {D : ℂ → ℂ} (hD : Continuous D) (hDc : HasCompactSupport D)
    (w : ℂ) : Integrable (fun ζ : ℂ => (w - ζ)⁻¹ * D ζ) := by
  have h0 : Integrable (fun ζ : ℂ => D ζ / (ζ - w)) :=
    Work.Analysis.RiemannSurface.integrable_div_sub hD hDc w
  refine (h0.neg).congr ?_
  filter_upwards with ζ
  rw [Pi.neg_apply, div_eq_mul_inv, show w - ζ = -(ζ - w) by ring, inv_neg, neg_mul,
    mul_comm (D ζ) ((ζ - w)⁻¹)]

/-- **Uniform bound on the Cauchy kernel.**  For continuous `D` with compact support there is a
constant `C` with `∫ ζ, ‖D ζ‖ ‖w - ζ‖⁻¹ ≤ C` for every `w`, and the integrand is integrable. -/
theorem kernel_uniform_bound (D : ℂ → ℂ) (hD : Continuous D) (hDc : HasCompactSupport D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, Integrable (fun ζ : ℂ => ‖D ζ‖ * ‖w - ζ‖⁻¹) ∧
      ∫ ζ : ℂ, ‖D ζ‖ * ‖w - ζ‖⁻¹ ≤ C := by
  obtain ⟨M, hM0, hM⟩ := Work.Analysis.Complex.DbarCauchy.exists_bound_of_cont_of_support hD
    hDc.isCompact (fun w hw => image_eq_zero_of_notMem_tsupport hw)
  have hIntD : Integrable (fun ζ : ℂ => ‖D ζ‖) :=
    hD.norm.integrable_of_hasCompactSupport hDc.norm
  have hIntD0 : 0 ≤ ∫ ζ : ℂ, ‖D ζ‖ := integral_nonneg fun _ => norm_nonneg _
  have htranslate : ∀ w : ℂ, ∫ ζ in Metric.ball w 1, ‖w - ζ‖⁻¹ = 2 * Real.pi := by
    intro w
    have hpt : ∀ ζ : ℂ, (Metric.ball w 1).indicator (fun ζ : ℂ => ‖w - ζ‖⁻¹) ζ
        = (fun η : ℂ => (Metric.ball (0 : ℂ) 1).indicator (fun η : ℂ => ‖η‖⁻¹) η) (w - ζ) := by
      intro ζ
      by_cases h : ζ ∈ Metric.ball w 1
      · have h' : w - ζ ∈ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm] at h ⊢
          rwa [sub_zero, norm_sub_rev]
        rw [Set.indicator_of_mem h]
        show ‖w - ζ‖⁻¹ = (Metric.ball (0 : ℂ) 1).indicator (fun η : ℂ => ‖η‖⁻¹) (w - ζ)
        rw [Set.indicator_of_mem h']
      · have h' : w - ζ ∉ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm] at h ⊢
          simp only [sub_zero]
          intro hc
          exact h (by rwa [norm_sub_rev] at hc)
        rw [Set.indicator_of_notMem h]
        show (0 : ℝ) = (Metric.ball (0 : ℂ) 1).indicator (fun η : ℂ => ‖η‖⁻¹) (w - ζ)
        rw [Set.indicator_of_notMem h']
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    rw [show (fun ζ : ℂ => (Metric.ball w 1).indicator (fun ζ : ℂ => ‖w - ζ‖⁻¹) ζ)
        = fun ζ : ℂ => (fun η : ℂ =>
            (Metric.ball (0 : ℂ) 1).indicator (fun η : ℂ => ‖η‖⁻¹) η) (w - ζ)
        from funext hpt]
    rw [show (fun ζ : ℂ => (fun η : ℂ =>
            (Metric.ball (0 : ℂ) 1).indicator (fun η : ℂ => ‖η‖⁻¹) η) (w - ζ))
        = fun ζ : ℂ => (fun η : ℂ =>
            (Metric.ball (0 : ℂ) 1).indicator (fun η : ℂ => ‖η‖⁻¹) η) (-ζ + w)
        from funext fun ζ => by rw [show -ζ + w = w - ζ by ring]]
    rw [MeasureTheory.integral_neg_eq_self
      (fun x : ℂ => (Metric.ball (0 : ℂ) 1).indicator (fun η : ℂ => ‖η‖⁻¹) (x + w)) volume]
    rw [MeasureTheory.integral_add_right_eq_self]
    rw [MeasureTheory.integral_indicator measurableSet_ball]
    exact integral_inv_norm_ball
  refine ⟨M * (2 * Real.pi) + ∫ ζ : ℂ, ‖D ζ‖,
    add_nonneg (mul_nonneg hM0 (by positivity)) hIntD0, fun w => ?_⟩
  have hIntw : Integrable (fun ζ : ℂ => ‖D ζ‖ * ‖w - ζ‖⁻¹) := by
    have h1 : Integrable (fun ζ : ℂ => ‖D ζ / (ζ - w)‖) :=
      (Work.Analysis.RiemannSurface.integrable_div_sub hD hDc w).norm
    refine h1.congr ?_
    filter_upwards with ζ
    rw [norm_div, norm_sub_rev, div_eq_mul_inv]
  refine ⟨hIntw, ?_⟩
  have hker : IntegrableOn (fun ζ : ℂ => M * ‖w - ζ‖⁻¹) (Metric.ball w 1) := by
    have h0 : IntegrableOn (fun ζ : ℂ => (ζ - w)⁻¹) (Metric.ball w 1) :=
      (Work.Analysis.RiemannSurface.integrableOn_inv_sub_compact (K := Metric.closedBall w 1)
        (isCompact_closedBall w 1) w).mono_set Metric.ball_subset_closedBall
    have h1 : IntegrableOn (fun ζ : ℂ => (w - ζ)⁻¹) (Metric.ball w 1) :=
      (h0.neg).congr_fun (fun ζ _ => by
        rw [Pi.neg_apply, show w - ζ = -(ζ - w) by ring, inv_neg]) measurableSet_ball
    have h2 : Integrable (fun ζ : ℂ => M * ‖(w - ζ)⁻¹‖) (volume.restrict (Metric.ball w 1)) :=
      h1.norm.const_mul M
    refine h2.congr ?_
    filter_upwards with ζ
    rw [norm_inv]
  rw [← MeasureTheory.integral_add_compl measurableSet_ball hIntw]
  refine add_le_add ?_ ?_
  · calc ∫ ζ in Metric.ball w 1, ‖D ζ‖ * ‖w - ζ‖⁻¹
        ≤ ∫ ζ in Metric.ball w 1, M * ‖w - ζ‖⁻¹ :=
          MeasureTheory.setIntegral_mono_on hIntw.integrableOn hker measurableSet_ball
            (fun ζ _ => mul_le_mul_of_nonneg_right (hM ζ) (by positivity))
      _ = M * (∫ ζ in Metric.ball w 1, ‖w - ζ‖⁻¹) := by rw [MeasureTheory.integral_const_mul]
      _ = M * (2 * Real.pi) := by rw [htranslate w]
  · refine le_trans (MeasureTheory.setIntegral_mono_on hIntw.integrableOn hIntD.integrableOn
      measurableSet_ball.compl ?_) (MeasureTheory.setIntegral_le_integral hIntD
        (Eventually.of_forall fun ζ => norm_nonneg _))
    intro ζ hζ
    have h1 : 1 ≤ ‖w - ζ‖ := by
      rw [Set.mem_compl_iff, Metric.mem_ball, not_lt] at hζ
      rw [dist_eq_norm, norm_sub_rev] at hζ
      exact hζ
    calc ‖D ζ‖ * ‖w - ζ‖⁻¹ ≤ ‖D ζ‖ * 1 :=
          mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ h1) (norm_nonneg _)
      _ = ‖D ζ‖ := mul_one _

/-- **The joint integrand of Fubini is integrable.**  For `A`, `Bc`, `w` continuous on `[a, b]` and
`D` continuous with compact support, the function
`(θ, ζ) ↦ A θ * (Bc θ * ((w θ - ζ)⁻¹ * D ζ))` is integrable for the product of the (restricted)
Lebesgue measure on `[a, b]` and the area measure on `ℂ`. -/
theorem integrable_curve_kernel (A Bc w : ℝ → ℂ) (D : ℂ → ℂ) {a b : ℝ}
    (hA : ContinuousOn A (Set.uIcc a b)) (hB : ContinuousOn Bc (Set.uIcc a b))
    (hw : ContinuousOn w (Set.uIcc a b)) (hD : Continuous D) (hDc : HasCompactSupport D) :
    Integrable (fun p : ℝ × ℂ => A p.1 * (Bc p.1 * ((w p.1 - p.2)⁻¹ * D p.2)))
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
  obtain ⟨C, hC0, hC⟩ := kernel_uniform_bound D hD hDc
  obtain ⟨MA, hMA⟩ := isCompact_uIcc.exists_bound_of_continuousOn hA
  obtain ⟨MB, hMB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hB
  have hAB : ∀ θ ∈ Set.uIoc a b, ‖A θ‖ * ‖Bc θ‖ ≤ max MA 0 * max MB 0 := by
    intro θ hθ
    have hθ' := Set.uIoc_subset_uIcc hθ
    exact mul_le_mul (le_trans (hMA θ hθ') (le_max_left _ _))
      (le_trans (hMB θ hθ') (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  have hpm : AEStronglyMeasurable
      (fun p : ℝ × ℂ => A p.1 * (Bc p.1 * ((w p.1 - p.2)⁻¹ * D p.2)))
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
    have hAem : AEMeasurable A (volume.restrict (Set.uIoc a b)) :=
      (hA.mono Set.uIoc_subset_uIcc).aemeasurable measurableSet_uIoc
    have hBem : AEMeasurable Bc (volume.restrict (Set.uIoc a b)) :=
      (hB.mono Set.uIoc_subset_uIcc).aemeasurable measurableSet_uIoc
    have hwem : AEMeasurable w (volume.restrict (Set.uIoc a b)) :=
      (hw.mono Set.uIoc_subset_uIcc).aemeasurable measurableSet_uIoc
    have hDae : AEMeasurable (fun p : ℝ × ℂ => D p.2)
        ((volume.restrict (Set.uIoc a b)).prod volume) :=
      (hD.measurable.comp measurable_snd).aemeasurable
    have hsnd : AEMeasurable (fun p : ℝ × ℂ => p.2)
        ((volume.restrict (Set.uIoc a b)).prod volume) := measurable_snd.aemeasurable
    exact ((hAem.comp_fst.mul (hBem.comp_fst.mul
      ((hwem.comp_fst.sub hsnd).inv.mul hDae)))).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff hpm]
  constructor
  · filter_upwards with θ
    have hker : Integrable (fun ζ : ℂ => (w θ - ζ)⁻¹ * D ζ) := integrable_inv_sub_mul hD hDc (w θ)
    refine (hker.const_mul (A θ * Bc θ)).congr ?_
    filter_upwards with ζ
    ring
  · have hfin : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc]
          exact ENNReal.ofReal_lt_top⟩
    refine Integrable.mono' (g := fun _ : ℝ => max MA 0 * max MB 0 * C)
      (MeasureTheory.integrable_const_iff.mpr (Or.inr hfin))
      ((hpm.norm).integral_prod_right') ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with θ hθ
    rw [Real.norm_of_nonneg (integral_nonneg fun ζ => norm_nonneg _)]
    have h1 : ∫ ζ : ℂ, ‖A θ * (Bc θ * ((w θ - ζ)⁻¹ * D ζ))‖
        = ‖A θ‖ * ‖Bc θ‖ * ∫ ζ : ℂ, ‖(w θ - ζ)⁻¹‖ * ‖D ζ‖ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
      dsimp only
      rw [norm_mul, norm_mul, norm_mul]
      ring
    rw [h1]
    have h2 : ∫ ζ : ℂ, ‖(w θ - ζ)⁻¹‖ * ‖D ζ‖ ≤ C := by
      have h3 : ∫ ζ : ℂ, ‖(w θ - ζ)⁻¹‖ * ‖D ζ‖ = ∫ ζ : ℂ, ‖D ζ‖ * ‖w θ - ζ‖⁻¹ := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
        dsimp only
        rw [norm_inv, mul_comm]
      rw [h3]; exact (hC (w θ)).2
    have hX : 0 ≤ ∫ ζ : ℂ, ‖(w θ - ζ)⁻¹‖ * ‖D ζ‖ := integral_nonneg fun ζ => by positivity
    calc ‖A θ‖ * ‖Bc θ‖ * (∫ ζ : ℂ, ‖(w θ - ζ)⁻¹‖ * ‖D ζ‖)
        ≤ (max MA 0 * max MB 0) * C :=
          mul_le_mul (hAB θ hθ) h2 hX (by positivity)
      _ = max MA 0 * max MB 0 * C := rfl

/-- **Cauchy–Pompeiu in the form used below**: `∫ ζ, (w - ζ)⁻¹ ∂̄G ζ = 2π G w`. -/
lemma integral_sub_inv_mul_dbar (G : ℂ → ℂ) (hG1 : ContDiff ℝ 1 G) (hGc : HasCompactSupport G)
    (w : ℂ) : ∫ ζ : ℂ, (w - ζ)⁻¹ * Work.Analysis.Complex.DbarCauchy.dbar G ζ
      = ((2 * Real.pi : ℝ) : ℂ) * G w := by
  have h := Work.Analysis.Complex.DbarCauchy.dbar_representation G hG1 hGc w
  have h1 : ∫ ζ : ℂ, (w - ζ)⁻¹ * Work.Analysis.Complex.DbarCauchy.dbar G ζ
      = -∫ ζ : ℂ, Work.Analysis.Complex.DbarCauchy.dbar G ζ / (ζ - w) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    dsimp only
    rw [div_eq_mul_inv, show w - ζ = -(ζ - w) by ring, inv_neg, neg_mul,
      mul_comm ((ζ - w)⁻¹) (Work.Analysis.Complex.DbarCauchy.dbar G ζ)]
  rw [h1, h]
  ring

theorem dbar_wind_integral (g : ℂ → ℂ) (r : ℝ) (G : ℂ → ℂ) (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hG1 : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) :
    ∫ ζ : ℂ, Work.Repel.Koebe.wind g r ζ * Work.Analysis.Complex.DbarCauchy.dbar G ζ
      = -Complex.I * circleIntegral (fun z : ℂ => G (g z) * deriv g z) 0 r := by
  obtain ⟨hcdg, hcg⟩ := continuousOn_deriv_circle g r hr hg
  have hAc : ContinuousOn (fun θ : ℝ => deriv (circleMap 0 r) θ) (Set.uIcc 0 (2 * Real.pi)) := by
    rw [show (fun θ : ℝ => deriv (circleMap 0 r) θ)
        = fun θ => circleMap 0 r θ * Complex.I from funext fun θ => deriv_circleMap 0 r θ]
    exact ((continuous_circleMap 0 r).mul continuous_const).continuousOn
  have hD : Continuous (Work.Analysis.Complex.DbarCauchy.dbar G) :=
    Work.Analysis.Complex.DbarCauchy.continuous_dbar G hG1
  have hDc : HasCompactSupport (Work.Analysis.Complex.DbarCauchy.dbar G) :=
    Work.Analysis.Complex.DbarCauchy.hasCompactSupport_dbar G hGc
  have hint : Integrable (fun p : ℝ × ℂ => deriv (circleMap 0 r) p.1 *
      (deriv g (circleMap 0 r p.1) *
        ((g (circleMap 0 r p.1) - p.2)⁻¹ * Work.Analysis.Complex.DbarCauchy.dbar G p.2)))
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod volume) :=
    integrable_curve_kernel (fun θ => deriv (circleMap 0 r) θ)
      (fun θ => deriv g (circleMap 0 r θ)) (fun θ => g (circleMap 0 r θ))
      (Work.Analysis.Complex.DbarCauchy.dbar G) hAc hcdg hcg hD hDc
  have hswap := intervalIntegral_integral_swap (a := (0 : ℝ)) (b := 2 * Real.pi)
    (μ := volume) (f := fun θ ζ =>
      deriv (circleMap 0 r) θ *
        (deriv g (circleMap 0 r θ) *
          ((g (circleMap 0 r θ) - ζ)⁻¹ * Work.Analysis.Complex.DbarCauchy.dbar G ζ))) hint
  have hwind : ∀ ζ : ℂ, wind g r ζ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap 0 r) θ *
        (deriv g (circleMap 0 r θ) * (g (circleMap 0 r θ) - ζ)⁻¹) := by
    intro ζ
    simp only [wind, circleIntegral, smul_eq_mul, div_eq_mul_inv]
  have hconst : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ((2 * Real.pi : ℝ) : ℂ) = -Complex.I := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    rw [show ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) by push_cast; ring]
    field_simp
    rw [sq, Complex.I_mul_I]
    ring
  calc ∫ ζ : ℂ, wind g r ζ * Work.Analysis.Complex.DbarCauchy.dbar G ζ
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ ζ : ℂ, (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap 0 r) θ *
            (deriv g (circleMap 0 r θ) * (g (circleMap 0 r θ) - ζ)⁻¹)) *
            Work.Analysis.Complex.DbarCauchy.dbar G ζ := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
        dsimp only
        rw [hwind ζ]
        ring
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ ζ : ℂ, (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap 0 r) θ *
            (deriv g (circleMap 0 r θ) *
              ((g (circleMap 0 r θ) - ζ)⁻¹ * Work.Analysis.Complex.DbarCauchy.dbar G ζ))) := by
        congr 1
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
        dsimp only
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        ring
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ ζ : ℂ, deriv (circleMap 0 r) θ *
            (deriv g (circleMap 0 r θ) *
              ((g (circleMap 0 r θ) - ζ)⁻¹ * Work.Analysis.Complex.DbarCauchy.dbar G ζ)) := by
        rw [hswap]
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap 0 r) θ *
            (deriv g (circleMap 0 r θ) *
              (((2 * Real.pi : ℝ) : ℂ) * G (g (circleMap 0 r θ)))) := by
        congr 1
        refine intervalIntegral.integral_congr fun θ _ => ?_
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          integral_sub_inv_mul_dbar G hG1 hGc (g (circleMap 0 r θ))]
    _ = -Complex.I * circleIntegral (fun z : ℂ => G (g z) * deriv g z) 0 r := by
        rw [circleIntegral]
        simp only [smul_eq_mul]
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        rw [show (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (deriv (circleMap 0 r) θ * (deriv g (circleMap 0 r θ) *
                (((2 * Real.pi : ℝ) : ℂ) * G (g (circleMap 0 r θ)))))
            = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (((2 * Real.pi : ℝ) : ℂ))) *
              (deriv (circleMap 0 r) θ *
                (deriv g (circleMap 0 r θ) * G (g (circleMap 0 r θ)))) by ring,
          hconst]
        ring

end Work.Repel.Koebe

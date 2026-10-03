import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.MeanValue.circleMean

/-!
# The area mean value inequality for holomorphic functions

If `u : ℂ → ℂ` is complex differentiable on the disc `ball c ρ` and continuous on its closure, then

  `‖u c‖² * (π ρ²) ≤ ∫ w in ball c ρ, ‖u w‖²`,

i.e. `‖u c‖²` is at most the mean of `‖u‖²` over the disc.  This is the `L² → L^∞` bridge used by
the weighted `∂̄` (Hörmander) route to the Behnke--Stein divisor theorem.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.MeanValue

/-- A bound for an integral over the angular range `Ioo (-π) π` of `Complex.polarCoord.target` in
terms of a pointwise bound for the integrand. -/
theorem norm_setIntegral_Ioo_neg_pi_pi_le {F : ℝ → ℝ} {C : ℝ}
    (hF : ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi, ‖F θ‖ ≤ C) :
    ‖∫ θ in Set.Ioo (-Real.pi) Real.pi, F θ‖ ≤ C * (2 * Real.pi) := by
  have hreal : (volume : Measure ℝ).real (Set.Ioo (-Real.pi) Real.pi) = 2 * Real.pi := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
    (s := Set.Ioo (-Real.pi) Real.pi) (f := F) (C := C) measure_Ioo_lt_top hF
  rwa [hreal] at h

/-- **Area mean value inequality**, disc centred at the origin. -/
theorem norm_sq_mul_le_integral_ball_zero {u : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : DiffContOnCl ℂ u (Metric.ball 0 ρ)) :
    ‖u 0‖ ^ 2 * (Real.pi * ρ ^ 2) ≤ ∫ w in Metric.ball 0 ρ, ‖u w‖ ^ 2 := by
  set M : ℝ := ‖u 0‖ ^ 2 with hM
  have hcont : ContinuousOn (fun w => ‖u w‖ ^ 2) (Metric.closedBall 0 ρ) := by
    rw [← closure_ball 0 (ne_of_gt hρ)]
    exact (hu.2.norm).pow 2
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn hcont
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (Metric.mem_closedBall_self hρ.le))
  have hmeasB : MeasurableSet (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hmem_ball : ∀ p : ℝ × ℝ, p ∈ Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi →
      (Complex.polarCoord.symm p : ℂ) ∈ Metric.ball 0 ρ := by
    intro p hp
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
    exact hp.1.2
  have hcontSymm : ContinuousOn (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ))
      (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    have hfun : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ)) =
        fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [hfun]
    fun_prop
  -- (1) polar coordinates for the disc integral
  have hstep1 : ∫ w in Metric.ball 0 ρ, ‖u w‖ ^ 2
      = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm p) := by
    rw [← MeasureTheory.integral_indicator (s := Metric.ball 0 ρ) measurableSet_ball]
    rw [← Complex.integral_comp_polarCoord_symm
      (fun w : ℂ => (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2) w)]
    rw [show polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl]
    simp only [smul_eq_mul]
  -- (2) restrict the radial variable to (0, ρ)
  have hstep2 : ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm p)
      = ∫ p in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm p) := by
    have hmeasA : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
      measurableSet_Ioi.prod measurableSet_Ioo
    have hBA : (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi) ⊆
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
      fun p hp => ⟨hp.1.1, hp.2⟩
    have h1 : ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
              (Complex.polarCoord.symm p)
        = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
              (fun p => p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
                (Complex.polarCoord.symm p)) p := by
      refine MeasureTheory.setIntegral_congr_fun hmeasA (fun p hp => ?_)
      by_cases hpb : p ∈ Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi
      · rw [Set.indicator_of_mem hpb]
      · rw [Set.indicator_of_notMem hpb]
        have hge : ρ ≤ p.1 := by
          by_contra hlt
          exact hpb ⟨⟨hp.1, not_le.mp hlt⟩, hp.2⟩
        have hnot : (Complex.polarCoord.symm p : ℂ) ∉ Metric.ball 0 ρ := by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
          exact not_lt.mpr hge
        rw [Set.indicator_of_notMem hnot, mul_zero]
    rw [h1, MeasureTheory.setIntegral_indicator hmeasB, Set.inter_eq_right.mpr hBA]
  -- (3) Fubini
  have hIntB : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
        (Complex.polarCoord.symm p))
      (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    have hprod : (volume.prod volume) (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi) < ⊤ := by
      rw [MeasureTheory.Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    refine IntegrableOn.of_bound hprod ?_ (ρ * C) ?_
    · have hc : ContinuousOn (fun p : ℝ × ℝ => p.1 * ‖u (Complex.polarCoord.symm p)‖ ^ 2)
          (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
        refine continuous_fst.continuousOn.mul ?_
        refine ((hu.2.comp hcontSymm ?_).norm).pow 2
        intro p hp
        exact subset_closure (hmem_ball p hp)
      refine (hc.aestronglyMeasurable hmeasB).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hmeasB] with p hp
      rw [Set.indicator_of_mem (hmem_ball p hp)]
    · filter_upwards [MeasureTheory.ae_restrict_mem hmeasB] with p hp
      have hmb := hmem_ball p hp
      rw [Set.indicator_of_mem hmb, Real.norm_eq_abs, abs_mul,
        abs_of_pos hp.1.1, abs_of_nonneg (sq_nonneg _)]
      have hb := hC _ (Metric.ball_subset_closedBall hmb)
      rw [Real.norm_of_nonneg (sq_nonneg _)] at hb
      exact le_trans (mul_le_mul_of_nonneg_left hb hp.1.1.le)
        (mul_le_mul_of_nonneg_right hp.1.2.le hC0)
  have hstep3 : ∫ p in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm p)
      = ∫ r in Set.Ioo (0 : ℝ) ρ, r * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm (r, θ))) := by
    change (∫ p in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm p) ∂(volume.prod volume))
      = ∫ r in Set.Ioo (0 : ℝ) ρ, r * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm (r, θ)))
    rw [MeasureTheory.setIntegral_prod _ hIntB]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun r _ => ?_)
    rw [MeasureTheory.integral_const_mul]
  -- (4) the angular integral is at least `2 π M`
  have hinner : ∀ r ∈ Set.Ioo (0 : ℝ) ρ,
      2 * Real.pi * M ≤ ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
          (Complex.polarCoord.symm (r, θ)) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hrρ : r < ρ := hr.2
    have hcongr : ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm (r, θ))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi, ‖u (circleMap 0 r θ)‖ ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [Set.indicator_of_mem (by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hr0]
        exact hrρ)]
      congr 2
      rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_ofReal_mul_I]
    rw [hcongr, integral_Ioo_neg_pi_pi_eq_Ioc
      (by simpa only [circleMap] using periodic_circle u 0 r),
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact circle_mean_value_sq hr0 (hu.mono (Metric.ball_subset_ball hrρ.le))
  -- (5) integrate in the radial variable
  have hIntB' : Integrable
      (fun p : ℝ × ℝ => p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
        (Complex.polarCoord.symm p))
      ((volume.restrict (Set.Ioo (0 : ℝ) ρ)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hIntB
  have hIntInner : IntegrableOn (fun r : ℝ => r * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
        (Complex.polarCoord.symm (r, θ)))) (Set.Ioo (0 : ℝ) ρ) := by
    refine (hIntB'.integral_prod_left).congr (Filter.Eventually.of_forall (fun r => ?_))
    dsimp only
    rw [MeasureTheory.integral_const_mul]
  have hIntConst : IntegrableOn (fun r : ℝ => (2 * Real.pi * M) * r)
      (Set.Ioo (0 : ℝ) ρ) := by
    rw [show (fun r : ℝ => (2 * Real.pi * M) * r)
        = (fun _ : ℝ => 2 * Real.pi * M) * (fun r : ℝ => r) from rfl]
    exact ((MeasureTheory.integrableOn_const (C := 2 * Real.pi * M) (s := Set.Icc (0 : ℝ) ρ)
      (hs := (measure_Icc_lt_top (a := (0 : ℝ)) (b := ρ)).ne)).mul_continuousOn
      continuous_id.continuousOn isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have heval : ∫ r in Set.Ioo (0 : ℝ) ρ, (2 * Real.pi * M) * r = M * (Real.pi * ρ ^ 2) := by
    rw [MeasureTheory.setIntegral_congr_set (μ := volume) MeasureTheory.Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le hρ.le, intervalIntegral.integral_const_mul, integral_id]
    ring
  have hmono : ∫ r in Set.Ioo (0 : ℝ) ρ, (2 * Real.pi * M) * r
      ≤ ∫ r in Set.Ioo (0 : ℝ) ρ, r * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm (r, θ))) := by
    rw [← MeasureTheory.integral_indicator (s := Set.Ioo (0 : ℝ) ρ)
        (f := fun r => (2 * Real.pi * M) * r) measurableSet_Ioo,
      ← MeasureTheory.integral_indicator (s := Set.Ioo (0 : ℝ) ρ)
        (f := fun r => r * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm (r, θ)))) measurableSet_Ioo]
    refine MeasureTheory.integral_mono
      ((MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr hIntConst)
      ((MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr hIntInner) (fun r => ?_)
    by_cases hr : r ∈ Set.Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, mul_comm (2 * Real.pi * M) r]
      exact mul_le_mul_of_nonneg_left (hinner r hr) hr.1.le
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
  calc M * (Real.pi * ρ ^ 2)
      = ∫ r in Set.Ioo (0 : ℝ) ρ, (2 * Real.pi * M) * r := heval.symm
    _ ≤ ∫ r in Set.Ioo (0 : ℝ) ρ, r * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm (r, θ))) := hmono
    _ = ∫ p in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm p) := hstep3.symm
    _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 * (Metric.ball 0 ρ).indicator (fun w => ‖u w‖ ^ 2)
            (Complex.polarCoord.symm p) := hstep2.symm
    _ = ∫ w in Metric.ball 0 ρ, ‖u w‖ ^ 2 := hstep1.symm

/-- **Area mean value inequality for holomorphic functions.** -/
theorem norm_sq_mul_le_integral_ball {u : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : DiffContOnCl ℂ u (Metric.ball c ρ)) :
    ‖u c‖ ^ 2 * (Real.pi * ρ ^ 2) ≤ ∫ w in Metric.ball c ρ, ‖u w‖ ^ 2 := by
  have hshift : DiffContOnCl ℂ (fun w => u (c + w)) (Metric.ball 0 ρ) := by
    refine DiffContOnCl.comp hu ?_ ?_
    · exact ⟨fun w _ => ((differentiableAt_const c).add
        (differentiableAt_id (𝕜 := ℂ) (x := w))).differentiableWithinAt,
        (continuous_const.add continuous_id).continuousOn⟩
    · intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
      simpa using hw
  have hpt : ∀ y : ℂ, (Metric.ball c ρ).indicator (fun w => ‖u w‖ ^ 2) (c + y)
      = (Metric.ball 0 ρ).indicator (fun w => ‖u (c + w)‖ ^ 2) y := by
    intro y
    by_cases h : y ∈ Metric.ball 0 ρ
    · have h' : c + y ∈ Metric.ball c ρ := by
        rw [Metric.mem_ball, dist_eq_norm] at h ⊢
        simpa using h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
    · have h' : c + y ∉ Metric.ball c ρ := by
        rw [Metric.mem_ball, dist_eq_norm] at h ⊢
        simpa using h
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  have htrans : ∫ w in Metric.ball c ρ, ‖u w‖ ^ 2
      = ∫ w in Metric.ball 0 ρ, ‖u (c + w)‖ ^ 2 := by
    rw [← MeasureTheory.integral_indicator (s := Metric.ball c ρ) measurableSet_ball,
      ← MeasureTheory.integral_indicator (s := Metric.ball 0 ρ) measurableSet_ball]
    rw [(MeasureTheory.integral_add_left_eq_self
      (fun w : ℂ => (Metric.ball c ρ).indicator (fun w => ‖u w‖ ^ 2) w) c).symm]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [htrans]
  simpa using norm_sq_mul_le_integral_ball_zero hρ hshift

end Work.Analysis.Complex.MeanValue

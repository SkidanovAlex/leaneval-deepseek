import Mathlib
import Submission.Commons.Measure.Integral.lintegral_moving_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

open MeasureTheory Metric
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

/-- For an a.e.-measurable `A : ℝ^d → ℝ≥0∞` and a linear isometry `Φ : ℝⁿ → ℝ^d`, the slice
`w ↦ A (z + Φ w)` agrees a.e. with the measurable representative `hA.mk A` for a.e. `z`. -/
private lemma ae_slice_eq (d n : ℕ)
    (Φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (hΦ : ∀ y, ‖Φ y‖ = ‖y‖) {r : ℝ} (hr : 0 < r)
    (A : EuclideanSpace ℝ (Fin d) → ENNReal)
    (hA : AEMeasurable A (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      (fun w => A (z + Φ w)) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)]
      (fun w => hA.mk A (z + Φ w)) := by
  classical
  have hÃm : Measurable (hA.mk A) := hA.measurable_mk
  have hAe : A =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d)))] hA.mk A := hA.ae_eq_mk
  have hAe0 : (volume : Measure (EuclideanSpace ℝ (Fin d))) {x | A x ≠ hA.mk A x} = 0 := by
    simpa [ne_eq] using (MeasureTheory.ae_iff.mp hAe)
  obtain ⟨N, hsN, hNmeas, hN0⟩ := MeasureTheory.exists_measurable_superset_of_null hAe0
  have hNind_meas : Measurable (N.indicator (1 : EuclideanSpace ℝ (Fin d) → ENNReal)) :=
    Measurable.indicator measurable_const hNmeas
  have hMB := lintegral_moving_ball d n Φ hΦ hr
    (N.indicator (1 : EuclideanSpace ℝ (Fin d) → ENNReal)) hNind_meas.aemeasurable
  have hFint : ∫⁻ x, N.indicator (1 : EuclideanSpace ℝ (Fin d) → ENNReal) x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) = 0 := by
    rw [lintegral_indicator_one hNmeas]; exact hN0
  have hdouble : ∫⁻ z, ∫⁻ w, N.indicator (1 : EuclideanSpace ℝ (Fin d) → ENNReal) (z + Φ w)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) = 0 := by
    rw [hMB, hFint, mul_zero]
  have hΦmeas : Measurable (fun w : EuclideanSpace ℝ (Fin n) => Φ w) :=
    (Φ.continuous_of_finiteDimensional).measurable
  have hτmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
      p.1 + Φ p.2) := measurable_fst.add (hΦmeas.comp measurable_snd)
  have hφmeas : Measurable (fun z =>
      ∫⁻ w, N.indicator (1 : EuclideanSpace ℝ (Fin d) → ENNReal) (z + Φ w)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r))) := by
    apply Measurable.lintegral_prod_right
    show Measurable (Function.uncurry (fun z : EuclideanSpace ℝ (Fin d) =>
      fun w : EuclideanSpace ℝ (Fin n) =>
        N.indicator (1 : EuclideanSpace ℝ (Fin d) → ENNReal) (z + Φ w)))
    convert hNind_meas.comp hτmeas using 1
    funext p; rfl
  have hφae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ∫⁻ w, N.indicator (1 : EuclideanSpace ℝ (Fin d) → ENNReal) (z + Φ w)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)) = 0 :=
    (lintegral_eq_zero_iff hφmeas).mp hdouble
  filter_upwards [hφae] with z hz
  have hpremeas : MeasurableSet ((fun w : EuclideanSpace ℝ (Fin n) => z + Φ w) ⁻¹' N) :=
    hNmeas.preimage (measurable_const.add hΦmeas)
  have hz2 : ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r))
      ((fun w : EuclideanSpace ℝ (Fin n) => z + Φ w) ⁻¹' N) = 0 := by
    have h1 : (fun w : EuclideanSpace ℝ (Fin n) =>
        N.indicator (1 : EuclideanSpace ℝ (Fin d) → ENNReal) (z + Φ w))
        = ((fun w : EuclideanSpace ℝ (Fin n) => z + Φ w) ⁻¹' N).indicator
            (1 : EuclideanSpace ℝ (Fin n) → ENNReal) := by
      funext w
      simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    rw [h1, lintegral_indicator_one hpremeas] at hz
    exact hz
  show ∀ᵐ w ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)),
      A (z + Φ w) = hA.mk A (z + Φ w)
  rw [MeasureTheory.ae_iff]
  apply le_antisymm _ zero_le
  calc ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r))
        {w | ¬ (A (z + Φ w) = hA.mk A (z + Φ w))}
      ≤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r))
          ((fun w : EuclideanSpace ℝ (Fin n) => z + Φ w) ⁻¹' N) := by
        apply measure_mono
        intro w hw
        exact hsN hw
    _ = 0 := hz2

theorem lintegral_mul_le_moving_ball (d n : ℕ)
    (Φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (hΦ : ∀ y, ‖Φ y‖ = ‖y‖) {r : ℝ} (hr : 0 < r)
    (A B : EuclideanSpace ℝ (Fin d) → ENNReal)
    (hA : AEMeasurable A) (hB : AEMeasurable B) {C : ENNReal}
    (hC : ∀ z w, w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r → B (z + Φ w) ≤ C * B z) :
    MeasureTheory.lintegral MeasureTheory.volume (fun x => A x * B x)
      ≤ C * MeasureTheory.lintegral MeasureTheory.volume (fun z =>
          (ENNReal.ofReal
              (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal)⁻¹
            * (MeasureTheory.lintegral
                (MeasureTheory.volume.restrict
                  (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r))
                (fun w => A (z + Φ w)))
            * B z) := by
  classical
  set muB : Measure (EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) with hmuB
  set V : ENNReal := (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) with hV
  have hΦmeas : Measurable (fun w : EuclideanSpace ℝ (Fin n) => Φ w) :=
    (Φ.continuous_of_finiteDimensional).measurable
  have hVpos : V ≠ 0 := by
    rw [hV]
    exact (Metric.measure_ball_pos volume 0 hr).ne'
  have hVtop : V ≠ ⊤ := by
    rw [hV]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall) ?_)
    exact (isCompact_closedBall 0 r).measure_lt_top
  have hslice := ae_slice_eq d n Φ hΦ hr A hA
  have hgmeas : Measurable (fun z => ∫⁻ w, hA.mk A (z + Φ w) ∂muB) := by
    apply Measurable.lintegral_prod_right
    exact hA.measurable_mk.comp (measurable_fst.add (hΦmeas.comp measurable_snd))
  have hg_ae : (fun z => ∫⁻ w, A (z + Φ w) ∂muB)
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d)))]
      (fun z => ∫⁻ w, hA.mk A (z + Φ w) ∂muB) := by
    filter_upwards [hslice] with z hz
    exact lintegral_congr_ae hz
  have hg : AEMeasurable (fun z => ∫⁻ w, A (z + Φ w) ∂muB)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    AEMeasurable.congr hgmeas.aemeasurable hg_ae.symm
  have hgB : AEMeasurable (fun z => (∫⁻ w, A (z + Φ w) ∂muB) * B z)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := hg.mul hB
  have hinner : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      (∫⁻ w, A (z + Φ w) * B (z + Φ w) ∂muB) ≤
        C * ((∫⁻ w, A (z + Φ w) ∂muB) * B z) := by
    filter_upwards [hslice] with z hz
    have hzA : AEMeasurable (fun w => A (z + Φ w)) muB :=
      (hA.measurable_mk.comp (measurable_const.add hΦmeas)).aemeasurable.congr hz.symm
    have hzA2 : AEMeasurable (fun w => A (z + Φ w) * B z) muB :=
      hzA.mul aemeasurable_const
    calc (∫⁻ w, A (z + Φ w) * B (z + Φ w) ∂muB)
        ≤ ∫⁻ w, A (z + Φ w) * (C * B z) ∂muB := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem
            (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := r))] with w hw
          exact mul_le_mul_right (hC z w hw) _
      _ = C * ((∫⁻ w, A (z + Φ w) ∂muB) * B z) := by
          rw [show (fun w => A (z + Φ w) * (C * B z))
                = (fun w => C * (A (z + Φ w) * B z)) by
                funext w; rw [mul_left_comm]]
          rw [lintegral_const_mul'' C hzA2]
          rw [lintegral_mul_const'' (B z) hzA]
  have hD_le : (∫⁻ z, ∫⁻ w, A (z + Φ w) * B (z + Φ w) ∂muB) ≤
      C * ∫⁻ z, (∫⁻ w, A (z + Φ w) ∂muB) * B z := by
    calc (∫⁻ z, ∫⁻ w, A (z + Φ w) * B (z + Φ w) ∂muB)
        ≤ ∫⁻ z, C * ((∫⁻ w, A (z + Φ w) ∂muB) * B z) := lintegral_mono_ae hinner
      _ = C * ∫⁻ z, (∫⁻ w, A (z + Φ w) ∂muB) * B z := by
          rw [lintegral_const_mul'' C hgB]
  have hMB := lintegral_moving_ball d n Φ hΦ hr (fun x => A x * B x) (hA.mul hB)
  calc ∫⁻ x, A x * B x
      = V⁻¹ * (∫⁻ z, ∫⁻ w, A (z + Φ w) * B (z + Φ w) ∂muB) := by
          rw [hMB, ← hV, ENNReal.inv_mul_cancel_left hVpos hVtop]
    _ ≤ V⁻¹ * (C * ∫⁻ z, (∫⁻ w, A (z + Φ w) ∂muB) * B z) :=
          mul_le_mul_right hD_le _
    _ = C * (V⁻¹ * ∫⁻ z, (∫⁻ w, A (z + Φ w) ∂muB) * B z) := by
          rw [mul_left_comm]
    _ = C * ∫⁻ z, V⁻¹ * ((∫⁻ w, A (z + Φ w) ∂muB) * B z) := by
          rw [lintegral_const_mul'' V⁻¹ hgB]
    _ = C * ∫⁻ z, (ENNReal.ofReal V.toReal)⁻¹ * (∫⁻ w, A (z + Φ w) ∂muB) * B z := by
          congr 1
          rw [ENNReal.ofReal_toReal hVtop]
          apply lintegral_congr
          intro z
          rw [mul_assoc]

end Commons.Measure.Integral

import Mathlib
import Submission.Commons.Measure.Kernel.setAverage_abs_integral_mul_kernel_le2
import Submission.Commons.Measure.Kernel.setAverage_abs_pairing_mollMeasure_le2
import Submission.Commons.Measure.Kernel.integral_measure_closedBall_le
import Submission.Commons.Measure.EuclideanSpace.volume_ball_ratio_mul_pow_le
import Submission.Commons.Measure.Mollification.abs_pairing_le_of_support_subset
import Submission.Commons.Measure.Kernel.setAverage_integral_closedBall_le
import Submission.Commons.Measure.Kernel.setAverage_toReal_measure_closedBall_le
import Submission.Commons.Measure.Kernel.aemeasurable_integral_closedBall_abs

namespace Commons.Measure.Kernel

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem setAverage_abs_integral_mul_kernel_add_pairing_le {n : ℕ}
    {k f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {ε C R E₀ : ℝ}
    (hk : ∀ t, 0 ≤ k t) (hC : ∀ t, k t ≤ C) (hC0 : 0 ≤ C)
    (hε : 0 < ε) (hR : 0 < R) (hεR : ε ≤ R)
    (hks : ∀ t, k t ≠ 0 → t ∈ Metric.closedBall 0 ε)
    (hf : LocallyIntegrable f volume) (hE0 : 0 ≤ E₀)
    (hE : ∀ s' ∈ Set.Ioc (0:ℝ) R, (∫ w in Metric.ball x₀ s', |f w|) ≤ E₀ * s' ^ n)
    (ν : SignedMeasure (EuclideanSpace ℝ (Fin n)))
    (hF : ∀ s' ∈ Set.Ioc (0:ℝ) R,
        (ν.totalVariation (Metric.closedBall x₀ s')).toReal ≤ E₀ * s' ^ n)
    {s : ℝ} (hs : 0 < s) (hRs : s + ε ≤ R) :
    (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        |(∫ τ, k (x₀ + z - τ) * f τ) + (∫ᵛ τ, k (x₀ + z - τ) ∂•ν)|)
      ≤ 2 * (2 ^ n * C * E₀ * ε ^ n) := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s with hB
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ∫ τ, k (x₀ + z - τ) * f τ with hFdef
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ∫ᵛ τ, k (x₀ + z - τ) ∂•ν with hGdef
  set D1 : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ| with hD1def
  set D2 : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal with hD2def
  have hBmeas : MeasurableSet B := by rw [hB]; exact Metric.isOpen_ball.measurableSet
  have hBfin : volume B ≠ ∞ := by
    rw [hB]
    exact (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) s).measure_lt_top).ne
  have hBpos : 0 < volume.real B := by
    rw [Measure.real_def, hB]
    exact ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hs).ne' hBfin
  -- geometry: for `z ∈ B` the moving ball sits inside the large ball around `x₀`
  have hsubset : ∀ z ∈ B, Metric.closedBall (x₀ + z) ε ⊆ Metric.ball x₀ (s + ε) := by
    intro z hz τ hτ
    have hz' : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s := by rwa [hB] at hz
    have hz2 : ‖z‖ < s := by rwa [Metric.mem_ball, dist_zero_right] at hz'
    rw [Metric.mem_closedBall, dist_eq_norm] at hτ
    rw [Metric.mem_ball, dist_eq_norm]
    have hτ' : ‖τ - x₀ - z‖ ≤ ε := by
      rwa [show τ - (x₀ + z) = τ - x₀ - z by abel] at hτ
    have h2 : ‖τ - x₀‖ ≤ ‖τ - x₀ - z‖ + ‖z‖ := by
      calc ‖τ - x₀‖ = ‖(τ - x₀ - z) + z‖ := congrArg (fun w => ‖w‖) (by abel)
        _ ≤ ‖τ - x₀ - z‖ + ‖z‖ := norm_add_le _ _
    linarith
  have hsubset' : ∀ z ∈ B, Metric.closedBall (x₀ + z) ε ⊆ Metric.closedBall x₀ (s + ε) :=
    fun z hz => (hsubset z hz).trans Metric.ball_subset_closedBall
  have hintball : IntegrableOn (fun τ => |f τ|) (Metric.ball x₀ (s + ε)) volume := by
    have hc : Integrable (fun τ : EuclideanSpace ℝ (Fin n) => |f τ|)
        (volume.restrict (Metric.closedBall x₀ (s + ε))) := by
      simpa only [Real.norm_eq_abs] using
        (hf.integrableOn_isCompact (isCompact_closedBall x₀ (s + ε))).abs
    exact IntegrableOn.mono_set hc Metric.ball_subset_closedBall
  -- pointwise bounds for the two dominating functions
  have hD1le : ∀ z ∈ B, D1 z ≤ E₀ * (s + ε) ^ n := by
    intro z hz
    calc D1 z = ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ| := rfl
      _ ≤ ∫ τ in Metric.ball x₀ (s + ε), |f τ| :=
          setIntegral_mono_set hintball (Filter.Eventually.of_forall (fun τ => abs_nonneg _))
            (Filter.Eventually.of_forall (fun τ hτ => hsubset z hz hτ))
      _ ≤ E₀ * (s + ε) ^ n := hE (s + ε) ⟨by linarith, hRs⟩
  have hD2le : ∀ z ∈ B, D2 z ≤ E₀ * (s + ε) ^ n := by
    intro z hz
    have h1 : ν.totalVariation (Metric.closedBall (x₀ + z) ε)
        ≤ ν.totalVariation (Metric.closedBall x₀ (s + ε)) := measure_mono (hsubset' z hz)
    exact (ENNReal.toReal_mono (measure_ne_top _ _) h1).trans (hF (s + ε) ⟨by linarith, hRs⟩)
  -- the two pointwise bounds for the kernel integrals
  have hptF : ∀ z, |F z| ≤ C * D1 z := fun z =>
    abs_integral_kernel_le (k := k) (f := f) (x₀ := x₀) (z := z) (ε := ε) (C := C)
      hk hC hC0 hks hf
  have hptG : ∀ z, |G z| ≤ C * D2 z := fun z =>
    Commons.Measure.Mollification.abs_pairing_le_of_support_subset hk hC hC0 hks ν (x₀ + z)
  -- measurability and integrability of the dominating functions
  have hD1ae : AEMeasurable D1 volume :=
    Commons.Measure.Kernel.aemeasurable_integral_closedBall_abs hf
  have hD2ae : AEMeasurable D2 volume :=
    Commons.Measure.Kernel.aemeasurable_toReal_measure_closedBall ν.totalVariation x₀ ε
  have hD1int : IntegrableOn D1 B volume :=
    Measure.integrableOn_of_bounded hBfin hD1ae.aestronglyMeasurable (M := E₀ * (s + ε) ^ n)
      (by filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with z hz
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun τ => abs_nonneg _))]
          exact hD1le z hz)
  have hD2int : IntegrableOn D2 B volume :=
    Measure.integrableOn_of_bounded hBfin hD2ae.aestronglyMeasurable (M := E₀ * (s + ε) ^ n)
      (by filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with z hz
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          exact hD2le z hz)
  -- the two average bounds, converted to integral bounds
  have hI1 : (∫ z in B, D1 z) ≤ volume.real B * (2 ^ n * E₀ * ε ^ n) := by
    have h := setAverage_integral_closedBall_le (n := n) (f := f) (x₀ := x₀) (ε := ε)
      (E₀ := E₀) (R := R) hf hε hR hεR hE0 hE hs hRs
    rw [MeasureTheory.setAverage_eq, smul_eq_mul, inv_mul_le_iff₀ hBpos] at h
    exact h
  have hI2 : (∫ z in B, D2 z) ≤ volume.real B * (2 ^ n * E₀ * ε ^ n) := by
    have h := setAverage_toReal_measure_closedBall_le (n := n) ν (x₀ := x₀) (ε := ε)
      (E₀ := E₀) (R := R) hε hR hεR hE0 hF hs hRs
    rw [MeasureTheory.setAverage_eq, smul_eq_mul, inv_mul_le_iff₀ hBpos] at h
    exact h
  have hdom : IntegrableOn (fun z => C * (D1 z + D2 z)) B volume :=
    (hD1int.add hD2int).const_mul C
  have hpt : ∀ z, |F z + G z| ≤ C * (D1 z + D2 z) := fun z => by
    calc |F z + G z| ≤ |F z| + |G z| := abs_add_le _ _
      _ ≤ C * D1 z + C * D2 z := add_le_add (hptF z) (hptG z)
      _ = C * (D1 z + D2 z) := by ring
  rw [MeasureTheory.setAverage_eq, smul_eq_mul, inv_mul_le_iff₀ hBpos]
  calc ∫ z in B, |F z + G z|
      ≤ ∫ z in B, C * (D1 z + D2 z) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _)) hdom
          (Filter.Eventually.of_forall hpt)
    _ = C * ((∫ z in B, D1 z) + ∫ z in B, D2 z) := by
        rw [MeasureTheory.integral_const_mul (f := fun z => D1 z + D2 z),
          MeasureTheory.integral_add (f := D1) (g := D2) hD1int hD2int]
    _ ≤ C * (2 * (volume.real B * (2 ^ n * E₀ * ε ^ n))) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        calc (∫ z in B, D1 z) + ∫ z in B, D2 z
            ≤ volume.real B * (2 ^ n * E₀ * ε ^ n)
              + volume.real B * (2 ^ n * E₀ * ε ^ n) := add_le_add hI1 hI2
          _ = 2 * (volume.real B * (2 ^ n * E₀ * ε ^ n)) := by ring
    _ = volume.real B * (2 * (2 ^ n * C * E₀ * ε ^ n)) := by ring

end Commons.Measure.Kernel

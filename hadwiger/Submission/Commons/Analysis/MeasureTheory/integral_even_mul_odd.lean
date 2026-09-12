import Mathlib
import Submission.Commons.Analysis.MeasureTheory.reflSphere_measurePreserving

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical

namespace Commons.Analysis.MeasureTheory

/-- The antipodal map of the unit sphere, as a homeomorphism. -/
def antipodalSphere (V : Type*) [NormedAddCommGroup V] :
    Metric.sphere (0 : V) 1 ≃ₜ Metric.sphere (0 : V) 1 where
  toFun θ := ⟨-θ.1, by
    simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩
  invFun θ := ⟨-θ.1, by
    simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩
  left_inv θ := by
    apply Subtype.ext
    simp
  right_inv θ := by
    apply Subtype.ext
    simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

theorem integral_even_mul_odd
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    {f g : Metric.sphere (0 : V) 1 → ℝ}
    (hf_even : ∀ θ : Metric.sphere (0 : V) 1,
      f (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1) = f θ)
    (hg_odd : ∀ θ : Metric.sphere (0 : V) 1,
      g (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1) = - g θ) :
    (∫ θ : Metric.sphere (0 : V) 1, f θ * g θ ∂MeasureTheory.volume.toSphere) = 0 := by
  let S := Metric.sphere (0 : V) 1
  let μ : Measure S := MeasureTheory.volume.toSphere
  have hantMP : MeasurePreserving (antipodalSphere V : S → S) μ μ := by
    simpa [S, μ, antipodalSphere] using (reflSphere_measurePreserving (V := V))
  have hantME : MeasurableEmbedding (antipodalSphere V : S → S) := by
    simpa [S] using (antipodalSphere V).measurableEmbedding
  have hcomp :
      (∫ θ : S, (fun θ : S => f θ * g θ) ((antipodalSphere V : S → S) θ) ∂μ) =
        (∫ θ : S, f θ * g θ ∂μ) :=
    MeasurePreserving.integral_comp hantMP hantME (fun θ : S => f θ * g θ)
  have hflip : (∫ θ : S, f θ * g θ ∂μ) = - (∫ θ : S, f θ * g θ ∂μ) := by
    calc
      (∫ θ : S, f θ * g θ ∂μ)
          = ∫ θ : S, (fun θ : S => f θ * g θ) ((antipodalSphere V : S → S) θ) ∂μ := hcomp.symm
      _ = ∫ θ : S, - (f θ * g θ) ∂μ := by
          apply integral_congr_ae
          filter_upwards with θ
          simp [antipodalSphere]
          rw [hf_even θ, hg_odd θ]
          ring
      _ = - (∫ θ : S, f θ * g θ ∂μ) := by
          rw [integral_neg]
  linarith

end Commons.Analysis.MeasureTheory

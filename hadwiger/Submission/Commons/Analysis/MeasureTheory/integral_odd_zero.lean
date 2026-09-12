import Mathlib
import Submission.Commons.Analysis.MeasureTheory.integral_even_mul_odd

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical

namespace Commons.Analysis.MeasureTheory

theorem integral_odd_zero
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    {g : Metric.sphere (0 : V) 1 → ℝ}
    (hg_odd : ∀ θ : Metric.sphere (0 : V) 1,
      g (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : V) 1) = - g θ) :
    (∫ θ : Metric.sphere (0 : V) 1, g θ ∂MeasureTheory.volume.toSphere) = 0 := by
  let S := Metric.sphere (0 : V) 1
  let μ : Measure S := MeasureTheory.volume.toSphere
  -- The constant function 1 is even, so `integral_even_mul_odd` applies:
  -- an even function times an odd function integrates to zero.
  have h := integral_even_mul_odd (V := V) (f := fun _ : S => (1 : ℝ)) (g := g) (by
    intro θ
    simp) hg_odd
  have hcongr : (∫ θ : S, g θ ∂μ) = ∫ θ : S, (1 : ℝ) * g θ ∂μ := by
    apply integral_congr_ae
    filter_upwards with θ
    simp
  exact hcongr.trans h

end Commons.Analysis.MeasureTheory

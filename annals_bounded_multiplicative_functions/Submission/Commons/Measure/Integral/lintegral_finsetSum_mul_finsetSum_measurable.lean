import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

theorem lintegral_finsetSum_mul_finsetSum_measurable {α ι κ : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (s : Finset ι) (t : Finset κ) (u : ι → α → ENNReal)
    (v : κ → α → ENNReal) (hu : ∀ i ∈ s, Measurable (u i)) (hv : ∀ j ∈ t, Measurable (v j)) :
    MeasureTheory.lintegral μ (fun x => (∑ i ∈ s, u i x) * (∑ j ∈ t, v j x))
      = ∑ i ∈ s, ∑ j ∈ t, MeasureTheory.lintegral μ (fun x => u i x * v j x) := by
  have hfun : (fun x => (∑ i ∈ s, u i x) * (∑ j ∈ t, v j x))
      = (fun x => ∑ i ∈ s, ∑ j ∈ t, u i x * v j x) := by
    funext x
    rw [Finset.sum_mul_sum]
  rw [hfun]
  rw [MeasureTheory.lintegral_finsetSum (μ := μ) (s := s)
        (f := fun i => fun x => ∑ j ∈ t, u i x * v j x)
        (fun i hi => Finset.measurable_sum t (fun j hj => (hu i hi).mul (hv j hj)))]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [MeasureTheory.lintegral_finsetSum (μ := μ) (s := t)
        (f := fun j => fun x => u i x * v j x)
        (fun j hj => (hu i hi).mul (hv j hj))]

end Commons.Measure.Integral
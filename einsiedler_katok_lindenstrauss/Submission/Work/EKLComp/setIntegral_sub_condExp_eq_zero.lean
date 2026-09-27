import Mathlib

open MeasureTheory

namespace Work.EKLComp

/-- For `f : X → ℝ` integrable on a probability space and `U` an invariant measurable set,
the integral over `U` of `f - E(f | invariants T)` vanishes.  Both terms are integrals of `f`
over the `invariants T`-measurable set `U`: `setIntegral_condExp` identifies the second with the
first, and `Integrable.sub` plus the set-integral algebra gives the difference.
(The conclusion is phrased as `∫_U (f - h) = 0` rather than `∫_U f = ∫_U h` to match the use
site: the bad-set argument needs `∫_U (f - h) = 0` for a specific invariant `U`.) -/
theorem setIntegral_sub_condExp_eq_zero {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (T : X → X) (f : X → ℝ)
    (hf : MeasureTheory.Integrable f μ) (U : Set X) (hU : MeasurableSet U) (hUT : T ⁻¹' U = U) :
    ∫ x in U, (f x - MeasureTheory.condExp (MeasurableSpace.invariants T) μ f x) ∂μ = 0 := by
  -- `invariants T` is a sub-σ-algebra of the ambient one.
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› := MeasurableSpace.invariants_le T
  -- `U` is measurable w.r.t. `invariants T`, precisely because `T ⁻¹' U = U`.
  have hUm : MeasurableSet[MeasurableSpace.invariants T] U :=
    MeasurableSpace.measurableSet_invariants.2 ⟨hU, hUT⟩
  -- Split the integral over `U` of the difference; both summands are integrable on `U`.
  rw [integral_sub hf.integrableOn
        (integrable_condExp (μ := μ) (m := MeasurableSpace.invariants T) (f := f)).integrableOn,
      -- `setIntegral_condExp` identifies `∫_U E(f | invariants T)` with `∫_U f`.
      setIntegral_condExp hm hf hUm, sub_self]

end Work.EKLComp

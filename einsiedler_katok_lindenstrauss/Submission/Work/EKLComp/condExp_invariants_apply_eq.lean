import Mathlib

namespace Work.EKLComp

/-- The conditional expectation of `f` with respect to the σ-algebra `MeasurableSpace.invariants T`
of `T`-invariant sets is itself `T`-invariant.  Proof: `MeasureTheory.stronglyMeasurable_condExp`
says it is `StronglyMeasurable[MeasurableSpace.invariants T]`; `StronglyMeasurable.measurable`
turns that into `Measurable[MeasurableSpace.invariants T]`; then
`MeasurableSpace.comp_eq_of_measurable_invariants` (`ℝ` has measurable singletons) gives
`g ∘ T = g`. -/
theorem condExp_invariants_apply_eq {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (T : X → X) (f : X → ℝ) (x : X) :
    MeasureTheory.condExp (MeasurableSpace.invariants T) μ f (T x) =
      MeasureTheory.condExp (MeasurableSpace.invariants T) μ f x := by
  have h := MeasurableSpace.comp_eq_of_measurable_invariants
    (f := T) (g := fun y => MeasureTheory.condExp (MeasurableSpace.invariants T) μ f y)
    (MeasureTheory.stronglyMeasurable_condExp.measurable)
  exact congrFun h x

end Work.EKLComp

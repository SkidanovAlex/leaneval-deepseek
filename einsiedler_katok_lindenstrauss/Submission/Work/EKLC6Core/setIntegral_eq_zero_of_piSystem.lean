import Mathlib

namespace Work.EKLC6Core

/-- **Dynkin π-λ upgrade for vanishing set integrals.** If `m` is a sub-σ-algebra of the ambient
one, `π` a π-system of *`m`-measurable* sets containing `univ` and generating `m`, and
`∫_t u ∂κ = 0` for all `t ∈ π` with `u` `κ`-integrable, then `∫_A u ∂κ = 0` for every
`m`-measurable `A`. -/
theorem setIntegral_eq_zero_of_piSystem {α : Type*} [mα : MeasurableSpace α]
    {κ : MeasureTheory.Measure α} {π : Set (Set α)} {m : MeasurableSpace α}
    (hm : m ≤ mα) (h_eq : m = MeasurableSpace.generateFrom π)
    (hpi : ∀ t ∈ π, @MeasurableSet α m t) (hinter : IsPiSystem π)
    (h_univ : (Set.univ : Set α) ∈ π) {u : α → ℝ} (hu : MeasureTheory.Integrable u κ)
    (h : ∀ t ∈ π, ∫ y in t, u y ∂κ = 0) :
    ∀ t : Set α, @MeasurableSet α m t → ∫ y in t, u y ∂κ = 0 := by
  -- The total integral of `u` vanishes since `univ ∈ π`.
  have hu_eq : ∫ y, u y ∂κ = 0 := by
    simpa [MeasureTheory.setIntegral_univ] using h Set.univ h_univ
  -- Dynkin's π–λ theorem for the predicate "the set integral of `u` vanishes".
  refine MeasurableSpace.induction_on_inter (m := m) (s := π)
    (C := fun t (_ : @MeasurableSet α m t) => ∫ y in t, u y ∂κ = 0)
    h_eq hinter ?_ ?_ ?_ ?_
  · -- empty set
    simp
  · -- members of the π-system
    intro t ht
    exact h t ht
  · -- complement
    intro t htm ih
    rw [MeasureTheory.setIntegral_compl (hm t htm) hu, hu_eq, ih, sub_zero]
  · -- countable disjoint union
    intro f _hfd hfm ihf
    rw [MeasureTheory.integral_iUnion (fun i => hm (f i) (hfm i)) _hfd hu.integrableOn]
    simp [ihf]

end Work.EKLC6Core

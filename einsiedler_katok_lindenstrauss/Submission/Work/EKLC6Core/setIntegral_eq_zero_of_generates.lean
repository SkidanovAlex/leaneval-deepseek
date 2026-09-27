import Mathlib

set_option linter.unusedVariables false

namespace Work.EKLC6Core

open MeasureTheory

theorem setIntegral_eq_zero_of_generates {X : Type*} [MeasurableSpace X] (S : ℕ → Set X)
    (hS : ∀ n, MeasurableSet (S n)) (hπ : ∀ m n, ∃ k, S m ∩ S n = S k)
    (hU : ∃ k, S k = Set.univ)
    (hgen : MeasurableSpace.generateFrom (Set.range S) = (inferInstance : MeasurableSpace X))
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure ν] {h : X → ℝ}
    (hint : MeasureTheory.Integrable h ν)
    (hzero : ∀ n, ∫ x in S n, h x ∂ν = 0) :
    ∀ t, MeasurableSet t → ∫ x in t, h x ∂ν = 0 := by
  -- `range S` is a π-system: it is closed under binary intersections by `hπ`,
  have hpi : IsPiSystem (Set.range S) := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ -
    obtain ⟨k, hk⟩ := hπ m n
    exact ⟨k, hk.symm⟩
  -- and the total integral vanishes, since some `S k` is everything.
  have huniv : ∫ x, h x ∂ν = 0 := by
    obtain ⟨k, hk⟩ := hU
    have hk0 := hzero k
    rw [hk] at hk0
    simpa using hk0
  -- Dynkin's π–λ theorem with the predicate "the set integral of `h` vanishes".
  refine MeasurableSpace.induction_on_inter
    (C := fun t (_ : MeasurableSet t) => ∫ x in t, h x ∂ν = 0) hgen.symm hpi ?_ ?_ ?_ ?_
  · simp
  · rintro t ⟨n, rfl⟩
    exact hzero n
  · intro t htm ih
    rw [MeasureTheory.setIntegral_compl htm hint, ih, huniv]
    simp
  · intro f hfd hfm ihf
    rw [MeasureTheory.integral_iUnion (fun i => hfm i) hfd hint.integrableOn]
    simp [ihf]

end Work.EKLC6Core

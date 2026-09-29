import Mathlib.RingTheory.Algebraic.Integral

open scoped BigOperators

namespace Commons.RingTheory.IsAlgebraic

/-- A finite sum of algebraic elements of a commutative ring over a field is
algebraic. -/
lemma finset_sum {R A : Type*} [Field R] [CommRing A] [Algebra R A]
    {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i ∈ s, IsAlgebraic R (f i)) : IsAlgebraic R (∑ i ∈ s, f i) := by
  rw [isAlgebraic_iff_isIntegral]
  exact IsIntegral.sum f (fun i hi => (hf i hi).isIntegral)

end Commons.RingTheory.IsAlgebraic
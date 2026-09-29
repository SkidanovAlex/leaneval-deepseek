import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

namespace Commons.RingTheory.IsIntegral

lemma finset_sum {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, IsIntegral R (f i)) :
    IsIntegral R (∑ i ∈ s, f i) := by
  exact IsIntegral.sum f h

end Commons.RingTheory.IsIntegral
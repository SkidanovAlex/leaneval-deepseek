import Mathlib.RingTheory.Derivation.Basic

namespace Commons.RingTheory.Derivation

/-- A derivation is additive, hence commutes with finite sums. -/
theorem map_sum {R A M ι : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
    [Algebra R A] [Module A M] [Module R M] (D : Derivation R A M) (s : Finset ι) (f : ι → A) :
    D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i) := by
  exact _root_.map_sum D f s

end Commons.RingTheory.Derivation
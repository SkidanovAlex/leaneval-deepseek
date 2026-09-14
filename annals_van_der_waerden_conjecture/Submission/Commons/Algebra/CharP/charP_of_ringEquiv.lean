import Mathlib.Algebra.CharP.Algebra

namespace Commons.Algebra.CharP

/-- The characteristic of a ring is preserved under ring equivalence. -/
theorem charP_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : ℕ) [CharP R p] : CharP S p := by
  exact charP_of_injective_ringHom (f := e.toRingHom) e.injective p

end Commons.Algebra.CharP
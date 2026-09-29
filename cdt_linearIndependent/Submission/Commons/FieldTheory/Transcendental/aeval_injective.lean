import Mathlib.RingTheory.Algebraic.Basic

namespace Commons.FieldTheory.Transcendental

/-- Evaluation at a transcendental element is injective: if `x` is transcendental over `R`, then
`p ↦ p(x)` is an injective map on `R[X]`. -/
theorem aeval_injective {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} (hx : Transcendental R x) :
    Function.Injective (fun p : Polynomial R => (Polynomial.aeval x) p) := by
  exact transcendental_iff_injective.mp hx

end Commons.FieldTheory.Transcendental
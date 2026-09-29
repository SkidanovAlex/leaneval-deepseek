import Mathlib.RingTheory.Algebraic.Defs

namespace Commons.FieldTheory.Transcendental

/-- A polynomial evaluated at a transcendental element vanishes only if the polynomial does. -/
theorem aeval_eq_zero_iff {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} (hx : Transcendental R x) (p : Polynomial R) :
    (Polynomial.aeval x) p = 0 ↔ p = 0 := by
  rw [transcendental_iff] at hx
  exact ⟨hx p, fun h => by rw [h, map_zero]⟩

end Commons.FieldTheory.Transcendental
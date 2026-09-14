import Mathlib.RingTheory.Trace.Defs

namespace Commons.Algebra.Trace

/-- The trace of `1` in a finite free algebra is the rank of the algebra over the base ring. -/
theorem trace_one_eq_finrank {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] :
    Algebra.trace R A (1 : A) = (Module.finrank R A : R) := by
  rw [Algebra.trace_apply, map_one]
  simp

end Commons.Algebra.Trace
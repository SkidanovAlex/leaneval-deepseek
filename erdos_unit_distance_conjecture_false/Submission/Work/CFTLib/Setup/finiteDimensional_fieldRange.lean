import Mathlib

namespace Work.CFTLib.Setup

theorem finiteDimensional_fieldRange {K L L' : Type} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L'] (f : L →ₐ[K] L') [FiniteDimensional K L] : FiniteDimensional K ↥(f.fieldRange) := by
  -- `f` induces a `K`-algebra isomorphism `L ≃ₐ[K] f.fieldRange`; finite dimensionality
  -- transfers along its underlying linear equivalence.
  exact LinearEquiv.finiteDimensional f.equivFieldRange.toLinearEquiv

end Work.CFTLib.Setup

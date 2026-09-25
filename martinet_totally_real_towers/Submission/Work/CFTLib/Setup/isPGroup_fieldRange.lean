import Mathlib

namespace Work.CFTLib.Setup

/-- If the group of `K`-algebra automorphisms of `L` is a `p`-group, then so is the group of
`K`-algebra automorphisms of the field range of any `K`-algebra homomorphism `f : L →ₐ[K] L'`.

Since `L` is a field, any `K`-algebra homomorphism out of `L` is injective (it sends `1 ↦ 1`),
so `AlgHom.equivFieldRange f` is an isomorphism `L ≃ₐ[K] ↥f.fieldRange`; conjugating by it
transports the group structure, and `IsPGroup` is invariant under group isomorphism. -/
theorem isPGroup_fieldRange {K L L' : Type} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L'] (p : ℕ) (f : L →ₐ[K] L') (hP : IsPGroup p (L ≃ₐ[K] L)) : IsPGroup p (↥(f.fieldRange) ≃ₐ[K] ↥(f.fieldRange)) :=
  hP.of_equiv (AlgEquiv.autCongr (AlgHom.equivFieldRange f))

end Work.CFTLib.Setup

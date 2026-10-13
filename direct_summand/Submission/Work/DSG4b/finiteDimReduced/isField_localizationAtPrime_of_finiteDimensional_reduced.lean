import Mathlib

namespace Work.DSG4b.finiteDimReduced

/-- **A finite-dimensional reduced algebra over a field, localised at a maximal ideal, is a
field.**  Equivalently (for a finite-dimensional reduced `k`-algebra `A`) the localisation
`A_m` at a maximal ideal `m` is a field, hence the canonical map `A ⧸ m → A_m` is an
isomorphism. -/
theorem isField_localizationAtPrime_of_finiteDimensional_reduced {k A : Type*} [Field k]
    [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A]
    (m : Ideal A) [m.IsMaximal] : IsField (Localization.AtPrime m) := by
  -- `A` is a finite module over the field `k`, hence an Artinian ring.
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- Localising an Artinian ring is Artinian, and localisation preserves reducedness;
  -- `A_m` is moreover local.  A commutative Artinian reduced local ring is a field.
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing _

end Work.DSG4b.finiteDimReduced

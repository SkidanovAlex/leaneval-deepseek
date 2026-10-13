import Mathlib

set_option linter.style.haveILetI false

namespace Work.DSM5b

/-- Integrality of `x` with respect to `f` is the same as integrality of `x` over the image
subring `f.range`, viewed as an extension of itself via the inclusion `f.range.subtype`.

The forward direction drops the coefficients: `f = (Subring.subtype f.range).comp f.rangeRestrict`,
so any integrality datum for `f` yields one for `f.range.subtype` by `RingHom.IsIntegralElem.of_comp`.

The backward direction is transitivity of integrality: `f.range` is integral over `R` (through
the surjective `f.rangeRestrict`), so an element integral over `f.range` is integral over `R`. -/
theorem isIntegralElem_range_subtype {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S) : f.IsIntegralElem x ↔ f.range.subtype.IsIntegralElem x := by
  constructor
  · intro h
    have h' : (Subring.subtype f.range).comp f.rangeRestrict = f := RingHom.ext fun r => rfl
    exact RingHom.IsIntegralElem.of_comp (g := Subring.subtype f.range) (f := f.rangeRestrict)
      (h' ▸ h)
  · intro h
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R f.range := f.rangeRestrict.toAlgebra
    haveI : IsScalarTower R f.range S :=
      IsScalarTower.of_algebraMap_eq' (by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]; rfl)
    haveI : Algebra.IsIntegral R f.range := by
      rw [← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
      exact RingHom.isIntegral_of_surjective _ f.rangeRestrict_surjective
    exact isIntegral_trans x h

end Work.DSM5b

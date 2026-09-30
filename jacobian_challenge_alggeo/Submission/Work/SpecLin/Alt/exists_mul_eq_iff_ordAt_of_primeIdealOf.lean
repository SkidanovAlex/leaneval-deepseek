import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.SpecLin.Alt.mem_range_algebraMap_iff_exists_mul_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Fractions over an affine open, and regularity at a place of that open

Let `C` be a smooth proper geometrically irreducible curve over a field `k`, let `U ⊆ C`
be a nonempty affine open and let `z` be a place of `C` whose point lies in `U`.  Write
`A = Γ(C, U)` and `P = (hU.primeIdealOf z).asIdeal` for the prime ideal of `A` cut out by
`z`.  Since `U` is affine, the local ring `𝒪_{C,z}` is the localization of `A` at `P`,
and the composite `A → 𝒪_{C,z} → K(C)` is a localization of the domain `A` at `P`.

The statement proved here is the resulting dictionary between the two ways of saying
that `x ∈ K(C)` is regular at `z`:

* `x` lies in the image of the localization of `A` at `P`, i.e. `x` can be written as a
  fraction `a / b` with `a, b ∈ A` and `b ∉ P` — this is the displayed
  `∃ a b, b ∉ P ∧ x * b = a`;
* the order of vanishing of `x` at `z` is nonnegative.

The first equivalence is `Work.SpecLin.Alt.mem_range_algebraMap_iff_exists_mul_eq` (pure
localization algebra, valid for any localization of a ring at a prime), and the second is
`Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff` (the local ring at a place is
a discrete valuation ring, so its image in `K(C)` is the unit ball of the associated
valuation).
-/

set_option linter.style.haveILetI false

namespace Work.SpecLin.Alt

/-- Over a nonempty affine open `U` of a curve, an element `x` of the function field is a
fraction `a / b` with `a, b ∈ Γ(C, U)` and `b` not in the prime ideal of `z` if and only if
`x` is regular at the place `z`. -/
theorem exists_mul_eq_iff_ordAt_of_primeIdealOf {k : Type*} [Field k]
    {C : Work.CurveBasics.Curve k}
    (U : C.left.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U]
    (z : C.Place) (hz : z.point ∈ U) (x : C.functionField) :
    (∃ a b : C.left.presheaf.obj (Opposite.op U),
        b ∉ (hU.primeIdealOf ⟨z.point, hz⟩).asIdeal ∧
        x * algebraMap (C.left.presheaf.obj (Opposite.op U)) C.functionField b
          = algebraMap (C.left.presheaf.obj (Opposite.op U)) C.functionField a)
      ↔ 0 ≤ C.ordAt x z := by
  -- Since `U` is affine, the local ring at `z` is the localization of `Γ(C, U)` at the
  -- prime ideal `P` of `z`, and the two maps to the function field form a scalar tower.
  letI : Algebra (C.left.presheaf.obj (Opposite.op U)) (C.left.presheaf.stalk z.point) :=
    C.left.presheaf.algebra_section_stalk ⟨z.point, hz⟩
  letI : IsLocalization.AtPrime (C.left.presheaf.stalk z.point)
      (hU.primeIdealOf ⟨z.point, hz⟩).asIdeal := hU.isLocalization_stalk ⟨z.point, hz⟩
  letI : IsScalarTower (C.left.presheaf.obj (Opposite.op U))
      (C.left.presheaf.stalk z.point) C.functionField :=
    AlgebraicGeometry.functionField_isScalarTower C.left U ⟨z.point, hz⟩
  -- Regularity at `z` is exactly membership in the image of the local ring `𝒪_{C,z}`.
  rw [← Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff C z x]
  -- And membership in the image of the localization is exactly the fraction condition.
  exact (Work.SpecLin.Alt.mem_range_algebraMap_iff_exists_mul_eq
    (R := C.left.presheaf.obj (Opposite.op U)) (S := C.left.presheaf.stalk z.point)
    (K := C.functionField) (hU.primeIdealOf ⟨z.point, hz⟩).asIdeal x).symm

end Work.SpecLin.Alt

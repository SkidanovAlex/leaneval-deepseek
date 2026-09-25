import Mathlib
import Submission.Work.Tower.CMAdjoin.Basic

/-!
# The minimal polynomial of `i` over the ring of integers of a totally real field

For a totally real number field `L`, the element `i ∈ K = L(i)` is a square root of `-1`,
and `X ^ 2 + 1` is its minimal polynomial not only over the field `L` but also over the
ring of integers `𝓞 L`.

## Main results

* `Work.Tower.CMAdjoin.minpoly_iota`: `minpoly L (iota L) = X ^ 2 + 1` (over the field).
* `Work.Tower.CMAdjoin.minpoly_iotaInt`: `minpoly (𝓞 L) (iotaInt L) = X ^ 2 + 1`
  (over the ring of integers), the requested lemma.

-/

open Polynomial NumberField

open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace CMAdjoin

/-- The minimal polynomial of `iota` over `L` is `X ^ 2 + 1`: the polynomial is monic and
irreducible over a totally real field, and `iota` is a root of it by construction. -/
theorem minpoly_iota (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    minpoly L (iota L) = sqAddOne L := by
  have hroot : Polynomial.aeval (iota L) (sqAddOne L) = 0 := by
    change Polynomial.aeval (AdjoinRoot.root (sqAddOne L)) (sqAddOne L) = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  exact (minpoly.eq_of_irreducible_of_monic (sqAddOne_irreducible L) hroot
    (sqAddOne_monic L)).symm

theorem minpoly_iotaInt (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    minpoly (NumberField.RingOfIntegers L) (Work.Tower.CMAdjoin.iotaInt L) =
      Polynomial.X ^ 2 + 1 := by
  -- `iotaInt` is integral over `𝓞 L`, since `𝓞 (L(i))` is integral over `𝓞 L`.
  have hint : IsIntegral (𝓞 L) (iotaInt L) := Algebra.IsIntegral.isIntegral _
  -- Over the fraction field `L`, the minimal polynomial of `iota` is `X ^ 2 + 1`.
  have hfield : minpoly L (iota L) = sqAddOne L := minpoly_iota L
  -- For an integrally closed base `𝓞 L`, the minimal polynomial over `𝓞 L` maps to the
  -- minimal polynomial over the fraction field `L`.
  have key := minpoly.isIntegrallyClosed_eq_field_fractions (R := 𝓞 L)
    (S := 𝓞 (cmAdjoin L)) L (cmAdjoin L) hint
  rw [show (algebraMap (𝓞 (cmAdjoin L)) (cmAdjoin L)) (iotaInt L) = iota L from rfl,
    hfield] at key
  -- `key : sqAddOne L = (minpoly (𝓞 L) (iotaInt L)).map (algebraMap (𝓞 L) L)`
  have hsq : (Polynomial.map (algebraMap (𝓞 L) L) (Polynomial.X ^ 2 + 1 : (𝓞 L)[X]))
      = sqAddOne L := by
    rw [sqAddOne_eq, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  -- The map `(𝓞 L)[X] → L[X]` is injective, so compare images.
  apply Polynomial.map_injective (algebraMap (𝓞 L) L) (IsFractionRing.injective (𝓞 L) L)
  rw [hsq]
  exact key.symm

end CMAdjoin
end Tower
end Work

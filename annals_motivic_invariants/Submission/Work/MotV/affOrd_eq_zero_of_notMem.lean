import Mathlib
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.AffPlaceSetup
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV.ordPlaceCommon

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-- An element `r` of the affine coordinate ring that does not lie in the maximal ideal
`⟨x - c, y - d⟩` is a unit of the local ring `affPlaceAt E c d`, hence its order of vanishing at
the affine place `(c, d)` is `0`. -/
theorem affOrd_eq_zero_of_notMem {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (c d : N) (h : WeierstrassCurve.Affine.Nonsingular E c d)
    (r : WeierstrassCurve.Affine.CoordinateRing E)
    (hr : r ∉ WeierstrassCurve.Affine.CoordinateRing.XYIdeal E c (Polynomial.C d)) :
    Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) (Work.MotC2.AffPlace N E c d h).1
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) r) = 0 := by
  haveI : Work.MotC2.IsNonsingularPoint E c d := ⟨h⟩
  haveI : IsDiscreteValuationRing ↥(Work.MotC2.affPlaceAt E c d) :=
    Work.MotC2.affPlaceAt_isDiscreteValuationRing E c d
  have hmem : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r ∈
      Work.MotC2.affPlaceAt E c d :=
    Work.MotC2.algebraMap_mem_affPlaceAt E c d r
  have hunit : IsUnit (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E c d) r) :=
    IsLocalization.map_units (M := (Work.MotC2.affPlaceIdeal E c d).primeCompl)
      (S := ↥(Work.MotC2.affPlaceAt E c d)) ⟨r, hr⟩
  -- the two descriptions of the same element of the local ring agree
  have heq : (⟨algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r, hmem⟩ :
      ↥(Work.MotC2.affPlaceAt E c d)) =
      algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E c d) r := by
    apply Subtype.ext
    exact rfl
  have hz : avNat (⟨algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r, hmem⟩ :
      ↥(Work.MotC2.affPlaceAt E c d)) = 0 := by
    rw [heq, ← IsUnit.unit_spec hunit]
    exact avNat_eq_zero_of_unit hunit.unit
  rw [ordOfPlace_eq_ordPlace,
    ordPlace_eq_of_mem E (Work.MotC2.affPlaceAt E c d) _ _ hmem, hz]
  norm_num

end Work.MotV

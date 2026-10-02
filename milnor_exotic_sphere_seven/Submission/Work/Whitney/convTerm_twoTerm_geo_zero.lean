import Mathlib
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Whitney.ChernRelSeries

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

namespace Work.Whitney

/-- **The `i = 0` summand of the convolution of `1 + z t` with the signed geometric series.**

The `0`-th summand of `convSeries (twoTermSeries z) (geoSeriesOf z) (m+1)` is the term
`(twoTermSeries z 0) ⌣ (geoSeriesOf z (m+1))`: its first factor is the unit `1` of `H^0`, and the
left unit law of the graded product (`Work.Cohomology.cupH'_one_left`) identifies it with
`geoSeriesOf z (m+1)`, all degree casts being the identity. -/
theorem convTerm_twoTerm_geo_zero {B : Type} [TopologicalSpace B] (z : Work.Thom.Coh ℤ 2 B) (m : ℕ) :
    Work.LerayHirsch.convTerm (Work.Whitney.ChernRel.twoTermSeries z)
        (Work.Whitney.ChernRel.geoSeriesOf z) (m + 1) 0
      = Work.Whitney.ChernRel.geoSeriesOf z (m + 1) := by
  rw [Work.LerayHirsch.convTerm_pos (Nat.zero_le _)]
  simp only [Work.Whitney.ChernRel.twoTermSeries_zero, Nat.mul_zero, Nat.sub_zero]
  rw [Work.Cohomology.cupH'_one_left]
  rw [Work.LerayHirsch.eqRec_eq_cohTransport, Work.Whitney.cohTransport_trans]
  rw [Work.LerayHirsch.cohTransport_congr_proof _ (rfl : 2 * (m + 1) = 2 * (m + 1))]
  exact Work.Thom.cohTransport_rfl _

end Work.Whitney

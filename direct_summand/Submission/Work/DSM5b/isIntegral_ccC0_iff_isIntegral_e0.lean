import Mathlib
import Submission.Work.DSM5b.CycleDefs
import Submission.Work.DSM5b.H0Defs

/-!
# DSM5b — `IsIntegral` of the `e0`-coordinate vs its `ccC0`-component

`e0` is `ccC0` followed by the transport `ccCast` of the chart ring along the identification
`ccIdx (ccConst i) = {i}` (`e0_apply`).  The forward map of `ccCast` is the algebra homomorphism
`ccRestr` and its inverse is `ccRestr` the other way; hence `ccCast` is an algebra isomorphism
and preserves and reflects integrality.  Consequently the two coordinates are integral at the
same time.
-/

namespace Work.DSM5b

universe a

open DSMap DSMap.Mix2

/-- The chart Čech coordinate transport `ccCast` (whose forward map is the algebra homomorphism
`ccRestr`) preserves and reflects integrality. -/
lemma isIntegral_ccCast_iff {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) {S T : Finset ι} (h : S = T) (y : ↥(chartRing t S)) :
    IsIntegral R (ccCast t h y) ↔ IsIntegral R y := by
  constructor
  · intro hx
    have h2 := IsIntegral.map (ccRestr t (le_of_eq h.symm)) hx
    rwa [show ccRestr t (le_of_eq h.symm) (ccCast t h y) = y from
      (ccCast t h).left_inv y] at h2
  · intro hy
    exact IsIntegral.map (ccRestr t (le_of_eq h)) hy

theorem isIntegral_ccC0_iff_isIntegral_e0 (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (i : ι) (z : (DSMap.Mix2.chartCech t).X 0) :
    IsIntegral R (Work.DSM5b.e0 R ι t z i) ↔
      IsIntegral R (Work.DSM5b.ccC0 R ι t z (fun _ : Fin 1 => i)) := by
  rw [e0_apply]
  exact isIntegral_ccCast_iff t (ccIdx_singleton (ccConst i)) (ccC0 R ι t z (ccConst i))

end Work.DSM5b

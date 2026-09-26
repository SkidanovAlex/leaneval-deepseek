import Mathlib
import Submission.Work.Topology.PlaneCurve.CruxBoundedComponentClean
import Submission.Work.Smooth.SphereJordan.jsepClean
import Submission.Work.Smooth.SphereJordan.boundedComponentWinding
import Submission.Work.Smooth.SphereJordan.boundedComponentExists

/-!
# Jordan separation, unconditionally and without `sorryAx`

`Work.Smooth.SphereJordan.exists_jsep_clean` is the `sorryAx`-free Jordan separation datum for a
continuous simple closed plane curve: the complement of the trace is the disjoint union of two
non-empty open preconnected sets, the unbounded side (where the winding number vanishes) and the
bounded side (where it is non-zero).

This declaration was extracted from `Submission.Work.Smooth.SphereJordan.cruxClean` (which is being
reduced to a re-export of `Submission.Work.Topology.PlaneCurve.CruxBoundedComponentClean`) so that it
has a single canonical home, reachable by `thetaGraph_two_components` and
`Work.BoxShrink.Pinch.filledRegion_properties`.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- **Jordan separation, unconditionally and without `sorryAx`.** -/
theorem exists_jsep_clean (γ : Work.Smooth.Jordan.PlaneCurve) (hγ : γ.IsSimple) :
    Nonempty (JSep γ) :=
  exists_jsep_of_wind_dict
    (fun {γ'} hγ' hper' hinj' {z'} hz' hbdd' =>
      windNumber_ne_zero_of_bounded_component hγ' hper' hinj' hz' hbdd')
    γ hγ

end

end Work.Smooth.SphereJordan

import Mathlib
import Submission.Work.Topology.PlaneCurve.CruxBoundedComponentClean

/-!
# A bounded complementary component of a simple closed plane curve is wound non-trivially

`Work.Topology.PlaneCurve.windNumber_ne_zero_of_bounded_component`: for a continuous `2π`-periodic
curve `γ : ℝ → ℂ` which is injective on one period `[0, 2π)` (a *Jordan curve*), every point `z` off
the trace whose connected component in the complement of the trace is *bounded* is wound around
non-trivially by `γ`.

This is the classical "the index of a Jordan curve is `±1` inside and `0` outside" statement in the
form needed here, and it is proved in `Submission/Work/Topology/PlaneCurve/CruxBoundedComponentClean.lean`
(as `Work.Smooth.SphereJordan.windNumber_ne_zero_of_bounded_component`), on top of the workspace's
Maehara/Brouwer development: the trap property
`Work.Smooth.SphereJordan.unbounded_component_of_curve_and_reflection` (a Jordan curve which is
antipodal-free and avoids `0` has an unbounded component of `0` off its trace and the trace of its
reflection), Janiszewski's theorem for disjoint compacta
(`Work.Smooth.JordanSeparation.janiszewski_disjoint`), Maehara's "at most two components"
(`Work.Topology.PlaneCurve.compl_jordan_atMostTwo`, built on the crossing lemma
`Work.Topology.PlaneCurve.plane_crossing_lemma`) and Maehara's lemma on the frontier of a
complementary component (`Work.Topology.PlaneCurve.frontier_component_eq_range`).  This module only
records the statement under the name and namespace requested by the requester.
-/

namespace Work.Topology.PlaneCurve

open Set

noncomputable section

theorem windNumber_ne_zero_of_bounded_component {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {z : ℂ} (hz : z ∉ Set.range γ)
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)) :
    Work.Smooth.SphereJordan.windNumber γ hγ z ≠ 0 :=
  Work.Smooth.SphereJordan.windNumber_ne_zero_of_bounded_component hγ hper hinj hz hbdd

end

end Work.Topology.PlaneCurve

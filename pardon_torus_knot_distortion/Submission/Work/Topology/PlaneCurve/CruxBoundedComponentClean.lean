import Mathlib
import Submission.Work.Topology.PlaneCurve.WindingTrapClean
import Submission.Work.Topology.PlaneCurve.UnboundedReflectionClean

/-!
# A bounded complementary component is wound non-trivially (cycle-free copy)

This is the statement of `Work.Smooth.SphereJordan.windNumber_ne_zero_of_bounded_component` from
`Submission/Work/Smooth/SphereJordan/cruxClean.lean`, packaged with an import closure that avoids
`Submission/Work/Topology/PlaneCurve/windNumber_ne_zero_of_normalized.lean`, so that the file
proving that statement can import this one.  The proof is the same: the "trap" form of the
statement together with the reflection argument.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- **A bounded complementary component forces a non-zero winding number.** -/
theorem windNumber_ne_zero_of_bounded_component {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {z : ℂ} (hz : z ∉ Set.range γ)
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)) :
    windNumber γ hγ z ≠ 0 :=
  windNumber_ne_zero_of_bounded_component_of_trap
    (fun hη hperη hinjη h0 hanti =>
      Work.Smooth.SphereJordan.unbounded_component_of_curve_and_reflection
        hη hperη hinjη h0 hanti)
    hγ hper hinj hz hbdd

end

end Work.Smooth.SphereJordan

import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.TorusCover.ParamTorus_exists_liftOf
import Submission.Work.BoxShrink.Pinch.DisjointLoopsWindingDet

namespace Work.PinchLemma3.ClosedDiscA

/-- **Two disjoint closed curves of a parametrised torus have proportional winding vectors.**

This is the form of `Work.BoxShrink.Pinch.DisjointLoopsWindingDet` in which the disjointness of
the two curves is phrased pointwise (`γ s ≠ δ t` for all `s`, `t`) and the vanishing of the
algebraic intersection number is written as the proportionality of the two winding vectors. -/
theorem winding_dependent_of_disjoint_curves {P : Work.CoreTopology.ParamTorus}
    {γ δ : Work.CoreTopology.ClosedCurve P}
    (hdis : ∀ s t : ℝ, γ.γ s ≠ δ.γ t) :
    (Work.SurgeryInvariance.windingOf P γ).1 * (Work.SurgeryInvariance.windingOf P δ).2 =
      (Work.SurgeryInvariance.windingOf P γ).2 * (Work.SurgeryInvariance.windingOf P δ).1 := by
  have hdisj : Disjoint (Set.range γ.γ) (Set.range δ.γ) := by
    rw [Set.disjoint_left]
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    exact hdis s t ht.symm
  exact sub_eq_zero.mp (Work.BoxShrink.Pinch.DisjointLoopsWindingDet P γ δ hdisj)

end Work.PinchLemma3.ClosedDiscA

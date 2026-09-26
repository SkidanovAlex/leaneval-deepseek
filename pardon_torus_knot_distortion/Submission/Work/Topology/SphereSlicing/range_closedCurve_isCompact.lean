import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

namespace Work.Topology.SphereSlicing

/-- A closed curve `γ : ClosedCurve P` is `2π`-periodic, hence its range is the image of the
compact interval `[0, 2π]`, hence compact. -/
theorem range_closedCurve_isCompact {P : Work.CoreTopology.ParamTorus}
    (γ : Work.CoreTopology.ClosedCurve P) : IsCompact (Set.range γ.γ) := by
  rw [← Function.Periodic.image_Icc γ.periodic (by positivity : (0 : ℝ) < 2 * Real.pi) 0,
    zero_add]
  exact isCompact_Icc.image γ.cont

end Work.Topology.SphereSlicing

import Mathlib
import Submission.Work.SphereJordan.odd_windNumber_of_mem_V
import Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane

namespace Work.Smooth.SphereJordan

/-- **The winding number of a simple closed plane curve about a point off the curve is `0` or
odd.**  Given the planar Jordan--Schoenflies theorem `h` as a hypothesis, every simple closed plane
curve `J` and every point `x` not on its trace: either `x` lies on the unbounded side, where the
winding number vanishes, or `x` lies on the bounded side, where (by
`Work.SphereJordan.odd_windNumber_of_mem_V`) the winding number is odd. -/
theorem windNumber_eq_zero_or_odd (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (J : Work.Smooth.Jordan.PlaneCurve) (hJ : J.IsSimple) {x : ℂ}
    (hx : x ∉ J.trace) :
    Work.Smooth.SphereJordan.windNumber J.γ J.cont x = 0 ∨
      Odd (Work.Smooth.SphereJordan.windNumber J.γ J.cont x) := by
  obtain ⟨S⟩ := h J hJ
  have hmem : x ∈ S.U ∪ S.V := by
    rw [S.union_eq]
    exact hx
  rcases hmem with hU | hV
  · exact Or.inl (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U S.toPlaneSeparation hU)
  · exact Or.inr (Work.SphereJordan.odd_windNumber_of_mem_V S hV)

end Work.Smooth.SphereJordan

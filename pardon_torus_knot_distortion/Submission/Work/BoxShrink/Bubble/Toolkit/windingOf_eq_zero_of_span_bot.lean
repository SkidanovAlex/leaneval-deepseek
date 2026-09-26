import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic

namespace Work.BoxShrink.Bubble.Toolkit

/-- A closed curve of the torus whose image lies in a region `X` of zero winding span is
null-homotopic: its winding vector vanishes. -/
theorem windingOf_eq_zero_of_span_bot
    {P : Work.CoreTopology.ParamTorus}
    {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.SurgeryInvariance.WindingSpan P X = ⊥)
    {γ : Work.CoreTopology.ClosedCurve P} (hγ : ∀ t : ℝ, γ t ∈ X) :
    Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
  have hmem : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈
      Work.SurgeryInvariance.WindingSpan P X :=
    Submodule.subset_span ⟨γ, hγ, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  exact Work.SurgeryInvariance.intPair_cast_eq_zero_iff (Work.SurgeryInvariance.windingOf P γ)
    |>.mp hmem

end Work.BoxShrink.Bubble.Toolkit

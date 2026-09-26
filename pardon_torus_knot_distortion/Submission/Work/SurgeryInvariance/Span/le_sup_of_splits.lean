import Mathlib
import Submission.Work.SurgeryInvariance.Defs

namespace Work.SurgeryInvariance.Span

/-- **Splitting a set of curves by a null-spanning region does not enlarge the winding span.**

If every closed curve of the torus lying in `A` lies either in `A'` or in `Z`, and `Z` spans
nothing (`WindingSpan P Z = ⊥`, i.e. `Z` contains no essential loop), then the winding span of
`A` is contained in that of `A'`: the winding vectors of curves in `A` either are winding
vectors of curves in `A'`, or vanish. -/
theorem le_sup_of_splits {P : Work.CoreTopology.ParamTorus}
    {A A' Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ A) → (∀ t : ℝ, γ t ∈ A') ∨ (∀ t : ℝ, γ t ∈ Z))
    (hZ : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.WindingSpan P A ≤ Work.SurgeryInvariance.WindingSpan P A' := by
  rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.WindingSpan]
  apply Submodule.span_le.mpr
  rintro v ⟨γ, hγ, rfl⟩
  rcases h γ hγ with hA' | hZ'
  · exact Submodule.subset_span ⟨γ, hA', rfl⟩
  · have hv : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
      rw [← hZ]
      exact Submodule.subset_span ⟨γ, hZ', rfl⟩
    rw [Submodule.mem_bot] at hv
    rw [hv]
    exact Submodule.zero_mem _

end Work.SurgeryInvariance.Span

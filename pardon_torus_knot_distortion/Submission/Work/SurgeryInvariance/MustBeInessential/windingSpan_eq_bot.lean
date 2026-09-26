import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.CoreTopology.MustBeInessential

namespace Work.SurgeryInvariance.MustBeInessential

/-- **Pardon's "mustbeinessential" lemma, in winding-span form.**

If the sphere `S` meets `β` in strictly fewer than `I(F, β)` points and the geometric
input `hclean` is available, then `S` contains no essential loop of the torus.  Since
`WindingSpan P X = ⊥` is exactly the statement that `X` contains no essential loop
(`WindingSpan_eq_bot_iff`), the winding span of `S` vanishes. -/
theorem windingSpan_eq_bot {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) (S : Set LeanEval.KnotTheory.PardonDistortion.R3)
    (hclean : ∀ α : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P α →
      (∀ t : ℝ, α.γ t ∈ S) →
      ∃ α' : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsSimple P α' ∧
        Work.CoreTopology.IsEssential P α' ∧ Work.CoreTopology.BoundsDiskInComplement P α' ∧
        Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤
          Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hSβ : Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β) :
    Work.SurgeryInvariance.WindingSpan P S = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hγ⟩
  exact Work.CoreTopology.mustbeinessential P β S hclean hSβ γ hγ hess

end Work.SurgeryInvariance.MustBeInessential

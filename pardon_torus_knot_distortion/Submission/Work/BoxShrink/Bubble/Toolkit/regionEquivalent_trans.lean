import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic

namespace Work.BoxShrink.Bubble.Toolkit

theorem regionEquivalent_trans
    {P : Work.CoreTopology.ParamTorus}
    {X Y Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h₁ : Work.SurgeryInvariance.RegionEquivalent P X Y)
    (h₂ : Work.SurgeryInvariance.RegionEquivalent P Y Z) :
    Work.SurgeryInvariance.RegionEquivalent P X Z := by
  refine ⟨?_, ?_⟩
  · intro γ hγ
    obtain ⟨γ', hγ', hw⟩ := h₁.1 γ hγ
    obtain ⟨γ'', hγ'', hw'⟩ := h₂.1 γ' hγ'
    exact ⟨γ'', hγ'', hw'.trans hw⟩
  · intro γ hγ
    obtain ⟨γ', hγ', hw⟩ := h₂.2 γ hγ
    obtain ⟨γ'', hγ'', hw'⟩ := h₁.2 γ' hγ'
    exact ⟨γ'', hγ'', hw'.trans hw⟩

end Work.BoxShrink.Bubble.Toolkit

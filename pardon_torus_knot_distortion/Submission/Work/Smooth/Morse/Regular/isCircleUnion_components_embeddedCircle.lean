import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Jordan.Defs

namespace Work.Smooth.Morse.Regular

theorem isCircleUnion_components_embeddedCircle (ψ : Submission.Diffeo) {Z : Set LeanEval.KnotTheory.PardonDistortion.R3} (h : Work.Smooth.Morse.IsCircleUnion ψ Z) : ∃ (n : ℕ) (c : Fin n → ℝ → LeanEval.KnotTheory.PardonDistortion.R3), (∀ i : Fin n, Work.Smooth.Jordan.IsEmbeddedCircle (Work.Smooth.Morse.torus ψ).carrier (Set.range (c i))) ∧ Z = ⋃ i, Set.range (c i) := by
  obtain ⟨n, γ, hsimple, -, hZ⟩ := h
  refine ⟨n, fun i => (γ i).γ, ?_, hZ⟩
  intro i
  refine ⟨?_, (γ i).γ, ⟨fun t => (γ i).mem t, (γ i).cont, (γ i).periodic, hsimple i⟩, rfl⟩
  rintro x ⟨t, rfl⟩
  exact (γ i).mem t

end Work.Smooth.Morse.Regular

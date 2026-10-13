import Mathlib
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE7

theorem cubeC_add {k k' : ℕ} (z : Fin (k + k') → ℝ) :
    z ∈ WilkiesDesign.E.cubeC (k + k') ↔
      WilkiesDesign.E.projFirst k k' z ∈ WilkiesDesign.E.cubeC k ∧
      WilkiesDesign.E.projSnd k k' z ∈ WilkiesDesign.E.cubeC k' := by
  constructor
  · intro hz
    exact ⟨fun i => hz _, fun i => hz _⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact h1 j
    · exact h2 j

end Work.WilE7

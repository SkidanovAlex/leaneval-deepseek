import Mathlib
import Submission.Work.SG.affFactsDefs

namespace Work.SG

/-- Conjugation by an affine map is a group action on sets of affine maps:
the identity acts trivially, and `conjAct` is compatible with multiplication. -/
theorem conjAct_action (d : ℕ) :
    (∀ S : Set (LeanEval.Geometry.SpaceGroupsProblem.AffineGroup d),
      Work.SG.AffFacts.conjAct (1 : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup d) S = S) ∧
    (∀ (ψ φ : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup d)
      (S : Set (LeanEval.Geometry.SpaceGroupsProblem.AffineGroup d)),
      Work.SG.AffFacts.conjAct (ψ * φ) S = Work.SG.AffFacts.conjAct ψ (Work.SG.AffFacts.conjAct φ S)) := by
  constructor
  · intro S
    ext h
    simp [Work.SG.AffFacts.conjAct]
  · intro ψ φ S
    ext h
    simp only [Work.SG.AffFacts.conjAct]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨φ * g * φ⁻¹, ⟨g, hg, rfl⟩, by group⟩
    · rintro ⟨k, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, by group⟩

end Work.SG

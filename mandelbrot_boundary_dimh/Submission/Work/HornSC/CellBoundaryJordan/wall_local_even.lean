import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs

namespace Work.HornSC.CellBoundaryJordan

theorem wall_local_even (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    ¬ ((hWallAt A (v.1, v.2) ∧ ¬ hWallAt A (v.1 - 1, v.2) ∧ ¬ vWallAt A (v.1, v.2)
          ∧ ¬ vWallAt A (v.1, v.2 - 1))
      ∨ (¬ hWallAt A (v.1, v.2) ∧ hWallAt A (v.1 - 1, v.2) ∧ ¬ vWallAt A (v.1, v.2)
          ∧ ¬ vWallAt A (v.1, v.2 - 1))
      ∨ (¬ hWallAt A (v.1, v.2) ∧ ¬ hWallAt A (v.1 - 1, v.2) ∧ vWallAt A (v.1, v.2)
          ∧ ¬ vWallAt A (v.1, v.2 - 1))
      ∨ (¬ hWallAt A (v.1, v.2) ∧ ¬ hWallAt A (v.1 - 1, v.2) ∧ ¬ vWallAt A (v.1, v.2)
          ∧ vWallAt A (v.1, v.2 - 1))
      ∨ (¬ hWallAt A (v.1, v.2) ∧ hWallAt A (v.1 - 1, v.2) ∧ vWallAt A (v.1, v.2)
          ∧ vWallAt A (v.1, v.2 - 1))
      ∨ (hWallAt A (v.1, v.2) ∧ ¬ hWallAt A (v.1 - 1, v.2) ∧ vWallAt A (v.1, v.2)
          ∧ vWallAt A (v.1, v.2 - 1))
      ∨ (hWallAt A (v.1, v.2) ∧ hWallAt A (v.1 - 1, v.2) ∧ ¬ vWallAt A (v.1, v.2)
          ∧ vWallAt A (v.1, v.2 - 1))
      ∨ (hWallAt A (v.1, v.2) ∧ hWallAt A (v.1 - 1, v.2) ∧ vWallAt A (v.1, v.2)
          ∧ ¬ vWallAt A (v.1, v.2 - 1))) := by
  simp only [hWallAt, vWallAt]
  tauto

end Work.HornSC.CellBoundaryJordan

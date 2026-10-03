import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.FreeGroupGens

theorem freeGens_one {α : Type*} : FreeGroup.gens (1 : FreeGroup α) = ∅ := by
  ext a
  simp [FreeGroup.gens, FreeGroup.toWord_one]

end Work.ORReductions.FreeGroupGens

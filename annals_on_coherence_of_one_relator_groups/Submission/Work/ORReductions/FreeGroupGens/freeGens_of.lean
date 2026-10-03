import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.FreeGroupGens

/-- The free generators occurring in a single generator `of a` are exactly `{a}`. -/
theorem freeGens_of {α : Type*} (a : α) : FreeGroup.gens (FreeGroup.of a) = {a} := by
  ext b
  simp [FreeGroup.gens, FreeGroup.toWord_of]

end Work.ORReductions.FreeGroupGens

import Mathlib

namespace Work.LinnikAreas

/-- A Dirichlet character of order dividing `2` takes only the values `0`, `1`, `-1`,
and those values are real. -/
theorem charValTri {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 = 1) (a : ZMod q) :
    (χ a = 0 ∨ χ a = 1 ∨ χ a = -1) ∧ (χ a).im = 0 := by
  have hq : MulChar.IsQuadratic χ := (MulChar.isQuadratic_iff_sq_eq_one (χ := χ)).mpr hχsq
  refine ⟨hq a, ?_⟩
  rcases hq a with h | h | h <;> simp [h]

end Work.LinnikAreas

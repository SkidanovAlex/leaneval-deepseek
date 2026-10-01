import Mathlib

namespace Work.LinnikAreas.FarRepel

/-- A Dirichlet character of order dividing two takes real values. -/
theorem imCharEqZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (u : ZMod q) : (χ u).im = 0 := by
  classical
  by_cases hu : IsUnit u
  · have h1 : (χ u) ^ 2 = (1 : MulChar (ZMod q) ℂ) u := by
      rw [← MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0) u, hχ2]
    rw [MulChar.one_apply hu] at h1
    rcases sq_eq_one_iff.mp h1 with h | h <;> rw [h] <;> simp
  · rw [MulChar.map_nonunit χ hu]
    simp

end Work.LinnikAreas.FarRepel

import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- The principal character of `ZMod q` is the indicator of the units: it takes the values `1`
and `0`, both real and in `[0,1]`, and dominates the modulus of every other Dirichlet character
pointwise. -/
theorem principal_apply_facts {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ((1 : DirichletCharacter ℂ q) n).im = 0 ∧ 0 ≤ ((1 : DirichletCharacter ℂ q) n).re ∧
    ((1 : DirichletCharacter ℂ q) n).re ≤ 1 ∧ ‖χ n‖ ≤ ((1 : DirichletCharacter ℂ q) n).re := by
  by_cases h : IsUnit (n : ZMod q)
  · have hone : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply h
    refine ⟨by rw [hone]; simp, by rw [hone]; simp, by rw [hone]; simp, ?_⟩
    rw [hone]
    simpa using DirichletCharacter.norm_le_one χ (n : ZMod q)
  · have h0 : (1 : DirichletCharacter ℂ q) n = 0 := MulChar.map_nonunit 1 h
    have h1 : χ n = 0 := MulChar.map_nonunit χ h
    refine ⟨by rw [h0]; simp, by rw [h0]; simp, by rw [h0]; simp, ?_⟩
    rw [h0, h1]
    simp

end Work.LinnikAreas.BGTZ

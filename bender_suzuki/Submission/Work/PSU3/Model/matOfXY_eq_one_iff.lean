import Mathlib
import Submission.Work.PSU3.Model

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.Model

open Matrix

theorem matOfXY_eq_one_iff {E : Type*} [Field E] [FrobeniusInvolution E] (x y : E) :
    matOfXY x y = 1 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h1 : matOfXY x y 0 1 = (1 : Matrix (Fin 3) (Fin 3) E) 0 1 := by rw [h]
    have h2 : matOfXY x y 0 2 = (1 : Matrix (Fin 3) (Fin 3) E) 0 2 := by rw [h]
    simp at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matOfXY]

end Work.PSU3.Model

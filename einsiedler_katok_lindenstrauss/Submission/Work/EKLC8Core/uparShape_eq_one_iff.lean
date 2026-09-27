import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open scoped Matrix

/-- The limit shape `uparShape p q r = [[1,p,q],[0,1,0],[0,r,1]]` is the identity of `SL₃(ℝ)`
exactly when its three parameters vanish. -/
theorem uparShape_eq_one_iff (p q r : ℝ) : uparShape p q r = 1 ↔ p = 0 ∧ q = 0 ∧ r = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ)) h
    simp only [Matrix.SpecialLinearGroup.coe_one] at h'
    refine ⟨?_, ?_, ?_⟩
    · have h01 := congrFun (congrFun h' 0) 1
      simpa [uparShape] using h01
    · have h02 := congrFun (congrFun h' 0) 2
      simpa [uparShape] using h02
    · have h21 := congrFun (congrFun h' 2) 1
      simpa [uparShape] using h21
  · rintro ⟨rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uparShape]

end Work.EKLC8Core

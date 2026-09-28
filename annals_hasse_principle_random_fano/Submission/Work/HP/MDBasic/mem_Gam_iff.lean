import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.MDBasic

theorem mem_Gam_iff (d n : ℕ) (x y : Fin (n + 1) → ℤ) (a : Mon d n → ℤ) :
    a ∈ Gam d n x y ↔ formEval d n a x = 0 ∧ formEval d n a y = 0 := by
  simp [Gam, latOrth, formEval, Fintype.linearCombination, Submodule.mem_inf]

end Work.HP.MDBasic

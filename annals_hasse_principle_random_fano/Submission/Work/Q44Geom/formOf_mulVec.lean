import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.Vero.MulDefs
import Submission.Work.HP.Vero.mulVec_formEval

set_option autoImplicit false

namespace Work.Q44Geom

open Work.HP

/-- The polynomial attached to a product coefficient vector is the product of the polynomials. -/
theorem formOf_mulVec {a b : ℕ} (A : Work.HP.Mon a 4 → ℤ) (B : Work.HP.Mon b 4 → ℤ) :
    Work.HP.formOf (a + b) 4 (Work.HP.Vero.mulVec a b (a + b) A B)
      = Work.HP.formOf a 4 A * Work.HP.formOf b 4 B := by
  have key := Work.HP.Vero.mulVec_formEval (a := a) (b := b) (n := 4)
      (R := MvPolynomial (Fin 5) ℚ) A B (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) ℚ)
  simp only [← Work.HP.aeval_formOf] at key
  rw [← map_mul] at key
  rwa [MvPolynomial.aeval_X_left_apply, MvPolynomial.aeval_X_left_apply] at key

end Work.Q44Geom

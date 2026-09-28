import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs

namespace Work.Q44Geom

open MvPolynomial

/-- The coefficientwise coercion `toRatLM` does not change the value of a form: evaluating the
rational polynomial `formOf 4 4 c` at `toRatLM v` agrees with the integral form evaluated at
`v` and then coerced to `ℚ`. -/
theorem formOf_eval (c : Work.HP.Mon 4 4 → ℤ) (v : Fin 5 → ℤ) :
    MvPolynomial.eval (Work.Q44Geom.toRatLM v) (Work.Q44Geom.f44 c)
      = ((Work.HP.formEval (R := ℤ) 4 4 c v : ℤ) : ℚ) := by
  rw [Work.Q44Geom.f44, ← MvPolynomial.aeval_eq_eval]
  rw [Work.HP.aeval_formOf]
  simp only [Work.HP.formEval, Work.HP.veronese, Work.Q44Geom.toRatLM, LinearMap.coe_mk,
    AddHom.coe_mk]
  push_cast
  rfl

end Work.Q44Geom

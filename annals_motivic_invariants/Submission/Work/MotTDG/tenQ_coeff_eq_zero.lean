import Mathlib
import Submission.Work.MotTDG.TenAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotTDG

theorem tenQ_coeff_eq_zero {L : Type*} [Field L] (a₁ a₃ : L) (c : Fin 10 → L)
    (h : tenQ a₁ a₃ c = 0) : c 2 = 0 ∧ c 4 = 0 ∧ c 6 = c 9 * a₃ ∧ c 8 = c 9 * a₁ := by
  -- `tenQ a₁ a₃ c = C (c 2) + C (c 4) * X + C (c 6) * X ^ 2 + C (c 8) * X ^ 3
  --   - C (c 9) * (C a₁ * X ^ 3 + C a₃ * X ^ 2)`, so read off the coefficients of `X ^ 0 … X ^ 3`.
  have h0 : c 2 = 0 := by
    have := congrArg (fun p : Polynomial L => p.coeff 0) h
    simpa [tenQ] using this
  have h1 : c 4 = 0 := by
    have := congrArg (fun p : Polynomial L => p.coeff 1) h
    simpa [tenQ] using this
  have h2 : c 6 - c 9 * a₃ = 0 := by
    have := congrArg (fun p : Polynomial L => p.coeff 2) h
    simpa [tenQ] using this
  have h3 : c 8 - c 9 * a₁ = 0 := by
    have := congrArg (fun p : Polynomial L => p.coeff 3) h
    simpa [tenQ] using this
  exact ⟨h0, h1, (sub_eq_zero.mp h2), (sub_eq_zero.mp h3)⟩

end Work.MotTDG

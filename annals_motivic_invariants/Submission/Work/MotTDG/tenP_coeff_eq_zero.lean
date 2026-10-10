import Mathlib
import Submission.Work.MotTDG.TenAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotTDG

theorem tenP_coeff_eq_zero {L : Type*} [Field L] (a₂ a₄ a₆ : L) (c : Fin 10 → L)
    (h : tenP a₂ a₄ a₆ c = 0) :
    c 0 = 0 ∧ c 1 = 0 ∧ c 3 = 0 ∧ c 5 = 0 ∧ c 7 = 0 ∧ c 9 = 0 := by
  -- `tenP` has coefficient `c 9` at `X ^ 5`, then `c 7 + c 9 * a₂` at `X ^ 4`, and so on.
  have h9 : c 9 = 0 := by
    have h9 : (tenP a₂ a₄ a₆ c).coeff 5 = 0 := by rw [h]; simp
    simpa [tenP] using h9
  have h7 : c 7 = 0 := by
    have h7 : (tenP a₂ a₄ a₆ c).coeff 4 = 0 := by rw [h]; simp
    simpa [tenP, h9] using h7
  have h5 : c 5 = 0 := by
    have h5 : (tenP a₂ a₄ a₆ c).coeff 3 = 0 := by rw [h]; simp
    simpa [tenP, h9] using h5
  have h3 : c 3 = 0 := by
    have h3 : (tenP a₂ a₄ a₆ c).coeff 2 = 0 := by rw [h]; simp
    simpa [tenP, h9] using h3
  have h1 : c 1 = 0 := by
    have h1 : (tenP a₂ a₄ a₆ c).coeff 1 = 0 := by rw [h]; simp
    simpa [tenP] using h1
  have h0 : c 0 = 0 := by
    have h0 : (tenP a₂ a₄ a₆ c).coeff 0 = 0 := by rw [h]; simp
    simpa [tenP] using h0
  exact ⟨h0, h1, h3, h5, h7, h9⟩

end Work.MotTDG

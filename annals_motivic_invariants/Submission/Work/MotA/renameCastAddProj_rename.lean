import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotA

noncomputable def renameCastAddProj (𝕜 : Type) [CommSemiring 𝕜] (n k : ℕ) : MvPolynomial (Fin (n + k)) 𝕜 →ₐ[𝕜] MvPolynomial (Fin n) 𝕜 := MvPolynomial.aeval fun i => if h : (i : ℕ) < n then MvPolynomial.X ⟨i.1, h⟩ else 0

theorem renameCastAddProj_rename (𝕜 : Type) [CommSemiring 𝕜] (n k : ℕ) (r : MvPolynomial (Fin n) 𝕜) : renameCastAddProj 𝕜 n k (MvPolynomial.rename (Fin.castAdd k) r) = r := by
  have h : ((fun (i : Fin (n + k)) => if h : (i : ℕ) < n then MvPolynomial.X ⟨i.1, h⟩ else (0 : MvPolynomial (Fin n) 𝕜))) ∘ Fin.castAdd k = (fun i => MvPolynomial.X i) := by
    funext i
    simp only [Function.comp_apply, Fin.val_castAdd, dite_eq_left i.isLt, Fin.eta]
  rw [show renameCastAddProj 𝕜 n k (MvPolynomial.rename (Fin.castAdd k) r) = MvPolynomial.aeval (((fun (i : Fin (n + k)) => if h : (i : ℕ) < n then MvPolynomial.X ⟨i.1, h⟩ else (0 : MvPolynomial (Fin n) 𝕜))) ∘ Fin.castAdd k) r from MvPolynomial.aeval_rename _ _ _]
  rw [h, MvPolynomial.aeval_X_left]
  rfl

end Work.MotA

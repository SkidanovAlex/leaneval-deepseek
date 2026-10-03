import Mathlib
import Submission.Work.Peluse.UControl.PetStepChain

namespace Work.Peluse.UControl

/-- **The initial state of the PET chain computes `LambdaMD`.**

`LambdaMDPetState N M P F` is the PET state whose parameter set is `Fin 1` (weight `1`), whose
slots are `Fin (P.natDegree - 1) ⊕ Fin 1` with shifts `y ↦ y^{i+1}` on the left summand and
`y ↦ P.eval y` on the right, base function `F 0` and slot functions `F (i+1)`, `F P.natDegree`.
Its correlation `PetState.lam` is therefore the single-term sum of the norm of `LambdaMD`, and the
product over the sum-slot-type splits into the paper's
`(∏_{i < d-1} F_{i+1}(x + y^{i+1})) · F_d(x + P(y))`. -/
theorem petChainMD {P : Polynomial ℤ} (N M : ℕ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    (Work.Peluse.UControl.PetStep.LambdaMDPetState N M P F).lam N M
      = ‖Work.Peluse.UControl.LambdaMD N M P F‖ := by
  dsimp only [Work.Peluse.UControl.PetStep.PetState.lam,
    Work.Peluse.UControl.PetStep.LambdaMDPetState, Work.Peluse.UControl.LambdaMD]
  rw [Fin.sum_univ_one]
  simp only [one_mul, Fintype.prod_sum_type, Fin.prod_univ_one]

end Work.Peluse.UControl

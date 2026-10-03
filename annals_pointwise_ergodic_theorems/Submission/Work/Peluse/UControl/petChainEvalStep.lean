import Mathlib
import Submission.Work.Peluse.UControl.PetStepChain

namespace Work.Peluse.UControl

/-- **The PET step commutes with the evaluation `PetStateP → PetState`.**

`PetStateP.step` builds the shifted polynomials `P_i(X + εh) - P_{i₀}` while `PetState.step` shifts
the evaluated functions `Q_i(y + εh) - Q_{i₀}(y)`, `Q_i = eval ∘ P_i`; the pointwise identity is
`Polynomial.eval_comp` (`(P.comp (X + C c)).eval y = P.eval (y + c)`) together with the case split
on `ε = j.1.2`, and the correlation `lam` is then a `sum_congr`/`tsum_congr`/`prod_congr` away. -/
theorem petChainEvalStep (S : Work.Peluse.UControl.PetStep.PetStateP) (i₀ : S.ι) (H N M : ℕ) :
    (S.step i₀ H).lam N M = (S.toState.step i₀ H).lam N M := by
  unfold PetStep.PetStateP.lam PetStep.PetState.lam
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  congr 1
  congr 1
  refine tsum_congr (fun x => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 1
  simp only [PetStep.PetStateP.step, PetStep.PetState.step, PetStep.PetStateP.toState,
    PetStep.stepQ]
  rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  by_cases h : (i.1).2 = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false, add_zero]

end Work.Peluse.UControl

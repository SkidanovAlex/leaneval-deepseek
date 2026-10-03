import Mathlib
import Submission.Work.Peluse.UControl.petInitDefs
import Submission.Work.Peluse.UControl.petChainMD

namespace Work.Peluse.UControl

open scoped BigOperators

set_option linter.unusedVariables false

/-- The coefficient ring of the initial symbolic state has no variables (`nv = 0`), so specialising
the `MvPolynomial` coefficients back to `ℤ` is the identity on polynomials. -/
lemma map_eval_param_zero (a : Fin 0 → ℤ) (p : Polynomial ℤ) :
    Polynomial.map (MvPolynomial.eval a) (Polynomial.map MvPolynomial.C p) = p := by
  rw [Polynomial.map_map]
  have h : ((MvPolynomial.eval a : MvPolynomial (Fin 0) ℤ →+* ℤ).comp MvPolynomial.C)
      = RingHom.id ℤ := by
    ext z
    simp
  rw [h, Polynomial.map_id]

/-- The shifts of the initial symbolic state evaluate at the trivial parameter to the shifts of
`LambdaMDPetState`: `y^(i+1)` on the power slots and `P.eval y` on the `P` slot. -/
lemma petInitQ_eval (P : Polynomial ℤ) (H : ℕ) (a : WinTower H 0)
    (i : (petInitSym P).S.ι) (y : ℤ) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval (WinTower.param H 0 a))
        (match i with
         | Sum.inl k => Polynomial.map MvPolynomial.C ((Polynomial.X : Polynomial ℤ) ^ (k.val + 1))
         | Sum.inr _ => Polynomial.map MvPolynomial.C P))
      = (match i with
         | Sum.inl k => y ^ (k.val + 1)
         | Sum.inr _ => Polynomial.eval y P) := by
  cases i with
  | inl k => rw [map_eval_param_zero]; simp
  | inr k => rw [map_eval_param_zero]

/-- **The initial symbolic state computes `LambdaMD`.**

The concrete state of the initial symbolic state (`nv = 0`, so its parameter set is the singleton
`WinTower H 0 = Fin 1`) has the same correlation as `LambdaMDPetState`: its weight is `1`, its base
function is `F 0`, its slot functions are `F (i+1)`, `F (P.natDegree)`, and — because there are no
formal parameters — its shift polynomials specialise back to `y^(i+1)` and `P`.  The claim then
follows from `petChainMD`. -/
theorem petInitSym_lam (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N M H : ℕ)
    (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    ((petInitSym P).S.toPetP H (petInitSlotF P F) (petInitBase H P F)).toState.lam N M
      = ‖LambdaMD N M P F‖ := by
  rw [PetStep.PetStateP.lam_eq]
  rw [← petChainMD N M F]
  dsimp only [PetStep.PetStateP.lam, PetStep.PetState.lam, PetStep.PetStateSym.toPetP,
    PetStep.LambdaMDPetState, petInitSym, petInitBase]
  simp only [WinTower.nu, one_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  congr 1
  refine tsum_congr (fun x => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hA := petInitQ_eval P H a i (y : ℤ)
  exact (congrArg (fun t => petInitSlotF P F i (x + t)) hA).trans rfl

end Work.Peluse.UControl

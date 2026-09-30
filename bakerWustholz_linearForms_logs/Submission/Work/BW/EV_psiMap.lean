import Mathlib
import Submission.Work.BW.subIdealDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

noncomputable section

/-- The `psiMap`-substitution is compatible with the constant subring: evaluating it at `(a, x)`
returns the constant back. -/
private lemma EV_psiMap_C {N m : ℕ} (ε : Bool) (c : Fin N → Fin m → ℤ) (a : ℂ)
    (x : Fin m → ℂˣ) (r : ℂ) :
    EV a x (psiMap ε c (MvPolynomial.C r)) = r := by
  simp [psiMap, EV, charEval, AddMonoidAlgebra.lift_single]

/-- The `psiMap`-substitution is compatible with the point `conePt (gammaPt ε c a x)`: evaluating
the substituted variable `X v` at `(a, x)` gives the `v`-th coordinate of the cone point. -/
private lemma EV_psiMap_X {N m : ℕ} (ε : Bool) (c : Fin N → Fin m → ℤ) (a : ℂ)
    (x : Fin m → ℂˣ) (v : Fin (N + 1) × Fin 2) :
    EV a x (psiMap ε c (MvPolynomial.X v)) =
      conePt N (gammaPt ε c a (fun j => (x j : ℂ))) v := by
  obtain ⟨i, b⟩ := v
  fin_cases b
  · simp [psiMap, MvPolynomial.aeval_X, conePt]
  · rw [psiMap, MvPolynomial.aeval_X]
    simp only [Fin.mk_one, conePt]
    rw [ite_eq_right (by decide : ¬((1 : Fin 2) = 0))]
    by_cases hi : i = 0
    · subst hi
      rw [dite_eq_left rfl, gammaPt, Fin.cons_zero]
      cases ε <;> simp [EV, charEval]
    · rw [dite_eq_right hi, gammaPt]
      conv_rhs => rw [← Fin.succ_pred i hi, Fin.cons_succ]
      simp [EV, charEval, AddMonoidAlgebra.lift_single, Units.coeHom]

/-- Evaluating the pull-back `psiMap ε c f` at the point `(a, x)` (the `G_a`-coordinate `u = a` and
the torus point `x`) coincides with evaluating `f` at the cone point over
`gammaPt ε c a x`. -/
lemma EV_psiMap {N m : ℕ} (ε : Bool) (c : Fin N → Fin m → ℤ) (a : ℂ) (x : Fin m → ℂˣ)
    (f : MR N) :
    EV a x (psiMap ε c f) =
      MvPolynomial.eval (conePt N (gammaPt ε c a (fun j => (x j : ℂ)))) f := by
  suffices h : (EV a x).comp (psiMap ε c : MR N →+* RingA m) =
      MvPolynomial.eval (conePt N (gammaPt ε c a (fun j => (x j : ℂ)))) by
    exact RingHom.congr_fun h f
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, MvPolynomial.eval_C]
    exact EV_psiMap_C ε c a x r
  · intro v
    rw [RingHom.comp_apply, MvPolynomial.eval_X]
    exact EV_psiMap_X ε c a x v

end

end Work.BW

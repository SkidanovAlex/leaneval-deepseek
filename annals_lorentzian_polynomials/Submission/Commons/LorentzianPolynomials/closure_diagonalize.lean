import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable

open Finsupp Matrix MvPolynomial UpperHalfPlane

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Commons.LorentzianPolynomials

/-- The diagonal map: substitute `X_j` by `X_i`, leaving every other variable fixed. -/
def closure_diagonalize_subst {n : ℕ} (i j : Fin n) : Fin n → MvPolynomial (Fin n) ℝ :=
  fun k => if k = j then MvPolynomial.X i else MvPolynomial.X k

/-- Evaluating at `z` the polynomial obtained by diagonalizing `i` and `j` is the same as
evaluating `f` at the point whose `j`-th coordinate is copied from the `i`-th one. -/
lemma closure_diagonalize_eval {n : ℕ} (i j : Fin n) (z : Fin n → ℍ)
    (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) (MvPolynomial.aeval (closure_diagonalize_subst i j) f) =
      MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘
        (fun k : Fin n => if k = j then z i else z k)) f := by
  classical
  have hcomp := MvPolynomial.comp_aeval_apply (R := ℝ) (S₁ := MvPolynomial (Fin n) ℝ)
    (σ := Fin n) (f := closure_diagonalize_subst i j)
    (φ := (MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z))) (p := f)
  rw [hcomp]
  have hfun : (fun k : Fin n => MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z)
        (closure_diagonalize_subst i j k)) =
      (((↑) : ℍ → ℂ) ∘ (fun k : Fin n => if k = j then z i else z k)) := by
    funext k
    by_cases hk : k = j
    · subst k
      simp [closure_diagonalize_subst]
    · simp [closure_diagonalize_subst, hk]
  rw [hfun]

theorem closure_diagonalize {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (f : MvPolynomial (Fin n) ℝ) (hf : Commons.LorentzianPolynomials.IsStable f) :
    Commons.LorentzianPolynomials.IsStable
      (MvPolynomial.aeval (fun k : Fin n => if k = j then MvPolynomial.X i else MvPolynomial.X k) f) := by
  classical
  rcases hf with hf0 | hfne
  · rw [hf0]
    simp [Commons.LorentzianPolynomials.IsStable]
  · right
    intro z
    change MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z)
      (MvPolynomial.aeval (closure_diagonalize_subst i j) f) ≠ 0
    rw [closure_diagonalize_eval i j z f]
    exact hfne (fun k : Fin n => if k = j then z i else z k)

end Commons.LorentzianPolynomials

end

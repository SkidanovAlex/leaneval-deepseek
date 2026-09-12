import Mathlib.Algebra.MvPolynomial.Rename

namespace Commons.Algebra.MvPolynomial

theorem surjective_aeval_dehom {k : Type} [Field k] (r : ℕ) :
    Function.Surjective (MvPolynomial.aeval (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) :
      MvPolynomial (Fin (r+1)) k →ₐ[k] MvPolynomial (Fin r) k) := by
  intro p
  refine ⟨MvPolynomial.rename Fin.succ p, ?_⟩
  rw [MvPolynomial.aeval_rename]
  have h : (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) ∘ Fin.succ
        = fun j : Fin r => MvPolynomial.X j := by
    funext j
    simp [Function.comp_apply]
  rw [h]
  exact MvPolynomial.aeval_X_left_apply p

end Commons.Algebra.MvPolynomial
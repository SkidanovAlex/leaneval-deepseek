import Mathlib
import Submission.Commons.Algebra.MvPolynomial.uniqueAlgEquiv_coeff
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_mul_le

namespace Commons.NumberTheory.Height.MvPolynomial

theorem logHeight_gP_uniqueAlgEquiv {σ : Type*} [Unique σ] [Fintype σ] (P : MvPolynomial σ ℚ) :
    Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP P) =
      Height.logHeight (fun o : Option ℕ =>
        o.elim 1 (fun m => (MvPolynomial.uniqueAlgEquiv ℚ σ P).coeff m)) := by
  classical
  have hfun : Commons.NumberTheory.Height.MvPolynomial.gP P =
      (fun o : Option ℕ => o.elim 1 (fun m => (MvPolynomial.uniqueAlgEquiv ℚ σ P).coeff m))
        ∘ ⇑(Equiv.optionCongr (Finsupp.uniqueEquiv (default : σ))) := by
    funext o
    cases o with
    | none =>
        simp only [Function.comp_apply, Equiv.optionCongr_apply, Option.map_none,
          Option.elim_none, Commons.NumberTheory.Height.MvPolynomial.gP]
    | some d =>
        simp only [Function.comp_apply, Equiv.optionCongr_apply, Option.map_some,
          Option.elim_some, Commons.NumberTheory.Height.MvPolynomial.gP,
          Finsupp.uniqueEquiv_apply]
        exact (Commons.Algebra.MvPolynomial.uniqueAlgEquiv_coeff P d).symm
  rw [hfun, Height.logHeight_comp_equiv]

end Commons.NumberTheory.Height.MvPolynomial

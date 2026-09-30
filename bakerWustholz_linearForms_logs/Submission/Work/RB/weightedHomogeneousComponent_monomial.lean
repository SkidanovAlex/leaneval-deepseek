import Mathlib
import Submission.Work.RB.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

open MvPolynomial

theorem weightedHomogeneousComponent_monomial {σ M R : Type*} [CommSemiring R] [AddCommMonoid M]
    [DecidableEq M] (w : σ → M) (n : M) (d : σ →₀ ℕ) (a : R) :
    MvPolynomial.weightedHomogeneousComponent w n (MvPolynomial.monomial d a) =
      if Finsupp.weight w d = n then MvPolynomial.monomial d a else 0 := by
  by_cases hw : Finsupp.weight w d = n
  · rw [ite_eq_left hw]
    exact IsWeightedHomogeneous.weightedHomogeneousComponent_same
      (isWeightedHomogeneous_monomial w d a hw)
  · rw [ite_eq_right hw]
    exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne n
      (isWeightedHomogeneous_monomial w d a rfl) (Ne.symm hw)

end Work.RB

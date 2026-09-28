import Mathlib
import Submission.Work.HP.Q44Setup

/-!
# Counting definitions for the quartic zero bound (`Work.HP.Q44Child`)

A nonzero quartic form in `5` variables has `O(T^4)` integral zeros of Euclidean norm at
most `T`.  The proof is an induction on the number of variables: a nonzero polynomial
`f` in `s+1` variables is written as `finSuccEquiv` of a univariate polynomial whose
coefficients are polynomials in `s` variables, and the box is split according to whether
the univariate fibre is identically zero or not.

This file only contains the shared definitions:

* `cbox s M` : the coordinate box `[-M,M]^s ⊆ ℤ^s`, as a `Finset`;
* `Cnt s f M` : the number of points of that box at which `f` vanishes;
* `formZ a`   : the integer polynomial with coefficient vector `a`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.Q44Child

/-- The coordinate box `[-M,M]^s ⊆ ℤ^s`, as a `Finset`. -/
def cbox (s M : ℕ) : Finset (Fin s → ℤ) :=
  Fintype.piFinset (fun _ : Fin s => Finset.Icc (-(M : ℤ)) (M : ℤ))

/-- The number of points of the coordinate box at which the polynomial `f` vanishes. -/
def Cnt (s : ℕ) (f : MvPolynomial (Fin s) ℤ) (M : ℕ) : ℕ :=
  ((cbox s M).filter (fun x => MvPolynomial.eval x f = 0)).card

/-- The coefficient vector of a degree-`d` form in `n+1` variables, as a polynomial over `ℤ`. -/
def formZ {d n : ℕ} (a : Mon d n → ℤ) : MvPolynomial (Fin (n + 1)) ℤ :=
  ∑ m : Mon d n, MvPolynomial.monomial m.toFinsupp (a m)

end Work.HP.Q44Child

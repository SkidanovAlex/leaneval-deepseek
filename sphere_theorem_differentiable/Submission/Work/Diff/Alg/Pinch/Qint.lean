import Mathlib
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integrand of Hamilton's reaction term `Q`

These are the two elementary pieces used in `Work.Diff.Alg.Pinch.Q_isAlgCurv` (the fact that
Hamilton's quadratic reaction term `Q R` of an algebraic curvature tensor is again an algebraic
curvature tensor).

With the component convention of `Submission.Diff.Alg` (`R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`),

`Q R i j k l = ∑ p, ∑ q, Qterm R i j k l p q`.

`Qterm` is the `(p,q)`-summand.  `Qbian` is the integrand of the first Bianchi identity of `Q R`:
the cyclic sum `Q R i j k l + Q R j k i l + Q R k i j l` is the double sum of `Qbian R i j k l p q`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The `(p,q)`-summand of Hamilton's reaction term:
`Qterm R i j k l p q = Rᵢⱼₚq Rₖₗₚq + 2 Rᵢₚₖq Rⱼₚₗq − 2 Rᵢₚₗq Rⱼₚₖq`. -/
noncomputable def Qterm (R : Curv4 n) (i j k l p q : Fin n) : ℝ :=
  R i j p q * R k l p q + 2 * R i p k q * R j p l q - 2 * R i p l q * R j p k q

/-- The `(p,q)`-integrand of the Bianchi identity of `Q R`:
`Qterm R i j k l p q + Qterm R j k i l p q + Qterm R k i j l p q`. -/
noncomputable def Qbian (R : Curv4 n) (i j k l p q : Fin n) : ℝ :=
  Qterm R i j k l p q + Qterm R j k i l p q + Qterm R k i j l p q

/-- `Q` unfolded into its double sum of integrands. -/
theorem Q_eq_sum_Qterm (R : Curv4 n) (i j k l : Fin n) :
    Q R i j k l = ∑ p, ∑ q, Qterm R i j k l p q := rfl

end Work.Diff.Alg.Pinch

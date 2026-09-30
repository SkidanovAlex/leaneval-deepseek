import Mathlib
import Submission.Work.BMF.kdr_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared vocabulary for `Work.BMF.VK2.mean_value_box`

`mvMom m x` is the vector of power sums of degrees `1, …, m` of an `s`-tuple
`x : Fin s → Finset.Icc 1 X`.  These are exactly the moment vectors that occur in the
expansion of the `s`-th power of the polynomial Weyl sum `polySum m α X`, and the count of
pairs of tuples with equal moment vectors is the Vinogradov mean-value count `J s m X`.
-/

namespace Work.BMF.VK2

open scoped BigOperators
open Finset

/-- The vector of power sums of degrees `1, …, m` of an `s`-tuple `x` with entries in `[1, X]`. -/
def mvMom (m : ℕ) {s X : ℕ} (x : Fin s → Finset.Icc 1 X) : Fin m → ℤ :=
  fun j => ∑ i, ((x i).1 : ℤ) ^ ((j : ℕ) + 1)

end Work.BMF.VK2

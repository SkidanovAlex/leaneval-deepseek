import Mathlib
import Submission.Work.Normal.Tricorn
import Submission.Work.Normal.juliaSet_comp_self
import Submission.Work.Normal.JuliaIterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Dynamics of the tricorn family via its holomorphic second iterate

The mandelbar family is antiholomorphic, so its Julia set is defined through normal families of the
antiholomorphic iterates.  Since `T̄_c ∘ T̄_c = TantibarSq c` is a holomorphic quartic polynomial
map, the whole holomorphic theory applies to `TantibarSq c`, and the two Julia sets agree.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial
open Polynomial

/-- The Julia set of the antiholomorphic quadratic map `T̄_c` is that of its holomorphic second
iterate `TantibarSq c`. -/
theorem juliaSet_tantibar_eq (c : ℂ) :
    JuliaSet (LeanEval.ComplexAnalysis.Tantibar c) = JuliaSet (TantibarSq c) := by
  rw [← tantibar_comp_self c]
  exact (juliaSet_comp_self (isCoerciveContinuous_tantibar c)).symm

/-- The `m`-th iterate of the tricorn quartic `TantibarSq c` is a polynomial map of degree
`4 ^ m`; this is the polynomial whose evaluation map is `(Tsq c)^[m]` in the sense of
`Polynomial.eval`. -/
theorem isPolynomialMapOfDegree_tantibarSq_iterate (c : ℂ) (m : ℕ) :
    IsPolynomialMapOfDegree (4 ^ m) ((TantibarSq c)^[m]) :=
  isPolynomialMapOfDegree_iterate (isPolynomialMapOfDegree_tantibarSq c) m

/-- The iterates of the holomorphic second iterate of the tricorn family are coercive continuous
maps, so they tend to `∞` at `∞` (used when transferring normality between the odd and even
iterates of `T̄_c`). -/
theorem isCoerciveContinuous_tantibarSq_iterate (c : ℂ) (m : ℕ) :
    IsCoerciveContinuous ((TantibarSq c)^[m]) :=
  isCoerciveContinuous_of_isPolynomialMapOfDegree
    (Nat.one_le_pow m 4 (by norm_num))
    (isPolynomialMapOfDegree_tantibarSq_iterate c m)

end Work.Normal

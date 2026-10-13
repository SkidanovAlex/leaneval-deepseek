import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Two-variable monomial sums

A continuous function on a set `s ⊆ ℝ × ℝ` is a *polynomial sum* if it is a finite sum of
two-variable monomials `c * z ^ a * θ ^ b` (with `a b : ℕ`).

These are exactly the polynomial functions in the two coordinate functions, and they form a
subalgebra of `C(s, ℝ)`.  This file only records the definition; the algebraic closure
properties live in the sibling files.
-/

namespace Work.FTS.GalBasis

open scoped BigOperators

/-- A continuous function on `s ⊆ ℝ × ℝ` which is a finite sum of two-variable monomials
`c * z ^ a * θ ^ b`. -/
def IsPolySum {s : Set (ℝ × ℝ)} (g : C(s, ℝ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → ℕ) (c : ι → ℝ),
    ∀ x : s, g x = ∑ i, c i * (x.1.1) ^ (a i) * (x.1.2) ^ (b i)

end Work.FTS.GalBasis

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

set_option autoImplicit false

open CategoryTheory Limits

namespace Work.ORCoherence

universe u

/-- The (left) global dimension of a ring `R`, as an element of `WithBot ℕ∞`:
the supremum of the projective dimensions of the left `R`-modules in the universe of `R`. -/
noncomputable def globalDim (R : Type u) [Ring R] : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} R), CategoryTheory.projectiveDimension M

end Work.ORCoherence

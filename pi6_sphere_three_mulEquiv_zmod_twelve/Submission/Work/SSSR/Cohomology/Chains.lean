import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory AlgebraicTopology
namespace Work.SSSR.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The singular chain complex of a topological space, with coefficients in `R`. -/
abbrev singularChains (X : TopCat) : ChainComplex (ModuleCat R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X

end

end Work.SSSR.Cohomology

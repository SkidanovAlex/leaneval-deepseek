import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.SSSR.Cohomology.Chains
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Cohomology
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology
namespace Work.SSSR.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The chain map of singular chains induced by a continuous map. -/
abbrev chainMap (X Y : TopCat) (f : X ⟶ Y) :
    singularChains R X ⟶ singularChains R Y :=
  ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map f

end

end Work.SSSR.Cohomology

import Mathlib
import Submission.Work.SSSR.RatHurewicz.Bridge.Defs
import Submission.Work.SSSR.RatHurewicz.Bridge.SigmaChain
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial
namespace Work.SSSR.Serre

noncomputable section

/-- The **simplicial boundary** of the standard `n`-simplex: the set of points with a vanishing
barycentric coordinate. -/
def simplexBdry (n : ℕ) : Set (↥(stdSimplex ℝ (Fin (n + 1)))) :=
  {z | ∃ j : Fin (n + 1), z.1 j = 0}

end

end Work.SSSR.Serre

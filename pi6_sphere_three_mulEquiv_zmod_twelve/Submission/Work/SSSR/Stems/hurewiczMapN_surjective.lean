import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Stems.SphereHomologyInject
import Submission.Work.Bordism.toSSet_coprod_iso
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.SSSR.Serre.simpHomExists
import Submission.Work.SSSR.Serre.simpHomChain
import Submission.Work.SSSR.Serre.prismHom_chain_identity
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Stems.HurewiczNeutralAgree
import Submission.Work.Stems.HurewiczMap
import Submission.Work.SSSR.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.RatHurewicz.Bridge.chainBoundary
import Submission.Work.RatHurewicz.Bridge.HomologyAux
import Submission.Work.SSSR.RatHurewicz.Bridge.SigmaChain
import Submission.Work.SSSR.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.SSSR.Serre.simpHomChain
import Submission.Work.Stems.HurewiczNeutralAgree
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Stems
variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial
namespace Work.SSSR.Stems

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The singular chain complex of `X` with `ℤ`-coefficients, in the presentation of area SERRE. -/
abbrev hChain (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat R) ℕ :=
  Work.SSSR.Serre.singChainC R X

open CategoryTheory
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

noncomputable section

end


set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators
namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial BigOperators
open Work.SSSR.RatHurewicz.Bridge (coface coface_apply)
namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators
namespace Work.SSSR.Stems.PerSimplex

open Work.SSSR.RatHurewicz.Bridge (coface coface_apply)
noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped BigOperators
open Work.SSSR.RatHurewicz.Bridge (coface coface_apply)
namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {n : ℕ}

end

end Work.SSSR.Stems.PerSimplex

namespace Work.SSSR.Stems.PerSimplex

end Work.SSSR.Stems.PerSimplex

namespace Work.SSSR.Stems.PerSimplex

open scoped Topology
end Work.SSSR.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators
namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval
namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators
namespace Work.SSSR.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

end

end Work.SSSR.Stems.PerSimplex

end

end Work.SSSR.Stems

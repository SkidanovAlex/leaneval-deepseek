import ChallengeDeps
import Submission.Helpers
import Submission.Work.RPV.Assemble
import Submission.Work.RPB.Nodes
import Submission.Work.RPA3.NodeCheck
import Submission.Work.RPCore.Nodes

/- The statement of `theorem_1` is elaborated in `Challenge.lean`, whose import set
(`ChallengeDeps`) does not contain the `CommCStarAlgebra` instance for `ℂ`; there the
`NormedCommRing ℂ` instance inside `𝓘(ℝ, ℂ)` is `NormedField.toNormedCommRing` and the
`NormedCommRing ℝ` instance is `Real.normedCommRing`.  The submission imports all of Mathlib,
where `CommCStarAlgebra.toNormedCommRing` (priority 1000) becomes the preferred
`NormedCommRing ℂ` instance.  The comparator checks `Solution.lean` against `Challenge.lean`
syntactically, so we raise `NormedField.toNormedCommRing` just above it, and `Real.normedCommRing`
above that (so that `ℝ` keeps its own instance), so that `Solution.lean` (which imports this
module) elaborates the statement with exactly the same instances as `Challenge.lean`. -/
attribute [instance 1001] NormedField.toNormedCommRing
attribute [instance 1002] Real.normedCommRing

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

namespace Submission

theorem theorem_1 (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ) :
    ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ), Similar (R z w θ) (R z' w' θ') ∧
    ∀ i : Fin 4, R z' w' θ' i ∈ Set.range γ :=
  Work.RPV.theorem_1_of_geometric_nodes
    (fun Hh Φ hΦ θ₀ h0 hπ => RectPeg.core Hh Φ hΦ θ₀ h0 hπ)
    Work.RPB.curveIsotopyNode Work.RPB.lagFamilyNode Work.RPA3.rpv_LagIsotopyNode γ z w θ hγ

end Submission

import Mathlib
import Submission.Work.Orient.Boundary.CoreIsoOfCollar
import Submission.Work.Orient.Boundary.RelFundClassOfInteriorCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT item 2 from the collar neighbourhood theorem

The two halves of ORIENT's item 2:

* `Work.Orient.Boundary.CoreIsoOfCollar` — the **geometric** half: the collar neighbourhood theorem
  (`Work.Surgery.HasCollar`, the named input of the Surgery area) gives `Work.Orient.CoreIsoProp n`,
  i.e. a compact core of the interior for which `H_{n+1}(W,∂W) → H_{n+1}(W, W∖C₀)` is an isomorphism;
* `Work.Orient.Boundary.RelativeFundamentalClassExists_of_coreIso` — the **orientation-theoretic**
  half: `CoreIsoProp n` gives `Work.Orient.RelativeFundamentalClassExists n`.

Combining them: from the collar neighbourhood theorem for compact `C^∞` manifolds with boundary,
every compact `C^∞` `(n+1)`-manifold `W` with boundary and an orientation (a family of local
generators, coherent over coordinate half-balls of the interior) has a relative fundamental class
`w ∈ H_{n+1}(W,∂W)` which is a local generator at every interior point and whose image under the
connecting homomorphism `hPairδ` is a fundamental class of `∂W` (the boundary-orientation
convention).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-- **Existence of the relative fundamental class, from the collar neighbourhood theorem.** -/
theorem RelativeFundamentalClassExists_of_hasCollar (n : ℕ)
    (h : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
      [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M],
      Work.Surgery.HasCollar n M) :
    Work.Orient.RelativeFundamentalClassExists n :=
  RelativeFundamentalClassExists_of_coreIso n (CoreIsoOfCollar n h)

end

end Work.Orient.Boundary

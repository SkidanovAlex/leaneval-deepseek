import Submission.Work.PTGeometric.localLevelPreimageTheorem
import Submission.Work.PTGeometric.Lvl.Manifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the **canonical manifold model** of a level set

`Work.PTGeometric.LocalLevelData k M W` is first-order data on the *set* `W`: at every point a local
smooth submersion cutting `W` out.  The preimage theorem
(`Work.PTGeometric.localLevelPreimageTheorem`) turns them into a compact `T2` smooth `9`-manifold with
boundary modelled on the half-space — and its proof (`Submission/Work/PTGeometric/Lvl/`) *builds that
manifold explicitly*: the underlying type is `↥W` and the charts are the submersion normal forms
(`Lvl.Setup.instChartedSpace`, `Lvl.Setup.instIsManifold`, `Lvl.Setup.mem_boundary_iff`,
`Lvl.Setup.instCompactSpace`).

This file names that model once and for all:

* `Work.PTGeometric.levelSetup W hW L` — the `Lvl.Setup` of the data;
* `Work.PTGeometric.levelModel W hW L` — its underlying type, definitionally `↥W`.

Why this matters (this is the reason the file exists): the orientation datum of the last mile
(`Work.PTGeometric.LevelOrientationData`) is an *existence* statement about a relative fundamental
class on a model of `W`.  Stated over an **arbitrary** model `W' ≃ₜ ↥W` (as earlier revisions did) it
quantifies over every smooth structure on a space homeomorphic to `W`, and is therefore *not*
derivable from the geometry: a non-orientable manifold carries no orientation family, and orientability
of a model is a statement about a smooth structure that a homeomorphism does not transport
constructively.  Stated over the **canonical** model it is a statement about one explicit manifold —
the one the preimage theorem builds — which is what the source construction can actually attack (its
charts are the submersion normal forms of the local data).

## Main definitions

* `Work.PTGeometric.levelSetup`, `Work.PTGeometric.levelModel`
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]

/-- **The local level-set data as a `Lvl.Setup`** (the input of the explicit chart construction of
`Submission/Work/PTGeometric/Lvl/`). -/
def levelSetup (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W) : Lvl.Setup k :=
  { M := M, W := W, isClosed_W := hWcl, data := L }

/-- **The canonical manifold model of the level set**: the subtype `↥W` with the charts built from the
submersion normal forms of the local data (`Submission/Work/PTGeometric/Lvl/`).  The instances are
`Lvl.Setup.instChartedSpace (levelSetup W hWcl L)`, `…instIsManifold`, `…instCompactSpace`, and the
boundary is characterised by `Work.PTGeometric.Lvl.Setup.mem_boundary_iff`. -/
abbrev levelModel (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W) : Type _ :=
  (levelSetup W hWcl L).Pre

/-- The canonical model is the subtype `↥W` (definitional). -/
theorem levelModel_eq_subtype (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W) :
    levelModel W hWcl L = ↥W := rfl

end

end Work.PTGeometric

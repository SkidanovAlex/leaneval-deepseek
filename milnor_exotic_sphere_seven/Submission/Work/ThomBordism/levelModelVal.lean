import Mathlib
import Submission.Work.PTGeometric.LevelModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Rewriting lemmas for the canonical level model (site glue)

`Work.PTGeometric.levelModel W hWcl L` is the abbreviation `(levelSetup W hWcl L).Pre`.  The
definitions of the setup's fields are `rfl`-visible only in a file whose `isDefEq` transparency is
the default; in the source construction (which sets
`backward.isDefEq.respectTransparency false`) the *defeq* steps through `levelSetup` are blocked.
These lemmas re-expose them as **rewrite rules**, which do not depend on transparency:

* `Work.ThomBordism.levelSetup_M` — `(levelSetup W hWcl L).M = M`;
* `Work.ThomBordism.levelSetup_W` — `(levelSetup W hWcl L).W = W`;
* `Work.ThomBordism.levelModel_val` — the underlying element of `x : levelModel W hWcl L` is `x.1`,
  and `w`-membership is membership in `W`.

No `sorry`, no new axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

namespace Work.ThomBordism

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]

/-- The ambient type of the level setup is the ambient manifold. -/
theorem levelSetup_M (W : Set M) (hWcl : IsClosed W) (L : Work.PTGeometric.LocalLevelData k M W) :
    (Work.PTGeometric.levelSetup W hWcl L).M = M := rfl

/-- The subset of the level setup is the level set. -/
theorem levelSetup_W (W : Set M) (hWcl : IsClosed W) (L : Work.PTGeometric.LocalLevelData k M W) :
    (Work.PTGeometric.levelSetup W hWcl L).W = W := rfl

/-- The underlying point of an element of the canonical level model. -/
theorem levelModel_val (W : Set M) (hWcl : IsClosed W)
    (L : Work.PTGeometric.LocalLevelData k M W) (x : Work.PTGeometric.levelModel W hWcl L) :
    (x : (Work.PTGeometric.levelSetup W hWcl L).M) = x.1 := rfl

/-- The underlying point of an element of the canonical level model lies in the level set. -/
theorem levelModel_coe_mem (W : Set M) (hWcl : IsClosed W)
    (L : Work.PTGeometric.LocalLevelData k M W) (x : Work.PTGeometric.levelModel W hWcl L) :
    (x.1 : M) ∈ W := x.2

end Work.ThomBordism


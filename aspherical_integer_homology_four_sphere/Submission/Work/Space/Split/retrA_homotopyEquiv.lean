import Mathlib
import Submission.Work.Space.Split
import Submission.Work.Space.Split.retrAUnroll
import Submission.Work.Space.Split.retrARetract
import Submission.Work.Space.Split.retrAHomotopy

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Topology
open unitInterval

namespace Work.Space.Split

/-- **`A` deformation retracts onto `M̄`.**

The unrolled model `U = M̄ ⊕ ⊔_v {1/4 < ‖p‖∞} × T_v` maps onto `A` by a quotient map; the
radial collapse of the shell onto the boundary of the square, followed by the inverse of the
gluing, descends to a retraction `r : A → M̄`, and the straight-line homotopy (which stays in the
shell because `1/4 < sqNorm ≤ 1`) descends to a homotopy from `i ∘ r` to the identity. -/
theorem retrA_homotopyEquiv (a : Assembly) :
    Nonempty (ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset} a.Mbar) :=
  a.retrA_homotopyEquiv_core

end Work.Space.Split

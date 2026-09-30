import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.uhsOfHyp_hypOfUHS

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Möbius transformation of the identity Lorentz matrix is the identity

`mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)` is the action on the upper half space model of the
Lorentz matrix `A`.  Here we record the trivial case `A = 1`: since `hypOfUHS` and `uhsOfHyp` are
mutually inverse on the upper half space (`uhsOfHyp_hypOfUHS`), the identity matrix acts as the
identity map.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix

theorem mobius_one (q : E4) (hq : 0 < q 3) : mobius 1 q = q := by
  have h3 : q 3 ≠ 0 := ne_of_gt hq
  simp only [mobius, Matrix.one_mulVec]
  exact uhsOfHyp_hypOfUHS h3

end Work.HypModel

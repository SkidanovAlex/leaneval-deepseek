import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.hypOfUHS_uhsOfHyp
import Submission.Work.HypModel.mobius_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Klein action is multiplicative

For `y` in the open unit ball, `hypOfKlein y` lies on the upper sheet of the hyperboloid, and a
Lorentz matrix preserving the upper sheet carries the upper sheet into itself
(`isLorentzMat_mem_upperSheet`).  Hence, writing `Q := B *ᵥ hypOfKlein y`, the two sides of

`mobiusKlein (A * B) y = mobius A (mobiusKlein B y)`

are `uhsOfHyp ((A * B) *ᵥ hypOfKlein y)` and `uhsOfHyp (A *ᵥ hypOfUHS (uhsOfHyp Q))`, which agree
because `hypOfUHS (uhsOfHyp Q) = Q` for `Q` on the upper sheet and `*ᵥ` is associative with the
matrix product.  This is the Klein-model counterpart of `mobius_mul`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix

/-- **The Klein action is multiplicative.** -/
theorem mobiusKlein_mul {A B : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (hB : IsLorentzMat B) {y : E4} (hy : y ∈ ball) :
    mobiusKlein (A * B) y = mobius A (mobiusKlein B y) := by
  have hP : hypOfKlein y ∈ upperSheet := hypOfKlein_mem_upperSheet hy
  have hQ : B *ᵥ hypOfKlein y ∈ upperSheet := isLorentzMat_mem_upperSheet hB hP
  rw [mobiusKlein, mobius, mobiusKlein, ← Matrix.mulVec_mulVec (hypOfKlein y) A B,
    hypOfUHS_uhsOfHyp hQ]

end Work.HypModel

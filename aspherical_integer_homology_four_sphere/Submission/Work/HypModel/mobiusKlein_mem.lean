import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.uhsOfHyp_three_pos
import Submission.Work.HypModel.mobius_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Matrix

namespace Work.HypModel

/-- **The Klein action stays in the upper half space.**  For a point `y` of the unit ball and a
Lorentz matrix `A` preserving the upper sheet, the image `mobiusKlein A y = uhsOfHyp (A *ᵥ (y,1)/√(1−|y|²))`
is a point of the upper half space model: its height coordinate is positive.  Indeed `hypOfKlein y`
lies on the upper sheet (`hypOfKlein_mem_upperSheet`), the Lorentz action carries the upper sheet
into itself (`isLorentzMat_mem_upperSheet`), and on the upper sheet the height is
`(P₄ − P₃)⁻¹ > 0` (`uhsOfHyp_three_pos`). -/
theorem mobiusKlein_mem {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) {y : E4}
    (hy : y ∈ ball) : 0 < (mobiusKlein A y) 3 := by
  have hP : hypOfKlein y ∈ upperSheet := hypOfKlein_mem_upperSheet hy
  have hQ : A *ᵥ hypOfKlein y ∈ upperSheet := isLorentzMat_mem_upperSheet hA hP
  simpa [mobiusKlein] using uhsOfHyp_three_pos hQ

end Work.HypModel

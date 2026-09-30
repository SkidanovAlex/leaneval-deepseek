import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `polarBox = {q | 1/4 < q 0 ∧ q 0 < rJ + 1}` is the preimage of the open interval
`(1/4, rJ + 1)` under the (continuous) first coordinate of `E4`, hence open. -/
theorem isOpen_polarBox : IsOpen polarBox := by
  have hcont : Continuous (fun q : E4 => q 0) := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
  have h : polarBox = (fun q : E4 => q 0) ⁻¹' Set.Ioo (1/4) (rJ + 1) := rfl
  rw [h]
  exact isOpen_Ioo.preimage hcont

end Work.Cusp

/-
# The core box `{√(q₀² + q₁²) < 1/2}` is open

The target of the core chart (`Work.Cusp.coreBox`) is the disk of radius `1/2` in the Cartesian
`(a,b)`-plane, the plane of the coordinates `q 0`, `q 1` of `E4 = ℝ⁴`.  In the warped metric
`dr² + f(r)²dθ² + h(r)²|dw|²` of the blueprint this is the region `r < 1/2`, where the profile is
`f(r) = r`, `h(r) = h₀`, i.e. the metric is flat.

It is an open box of the chart atlas, and this file records the only thing needed about it here:
it is open.  Both coordinates `q 0`, `q 1` are continuous on `E4` (they are the coordinate
projections of a PiLp space), hence so is the radius `r(q) = √(q₀² + q₁²)` (`Real.sqrt` is
continuous and `x ↦ x²` is), so `coreBox = r⁻¹' (Iio (1/2))` is open as the preimage of an open
interval of `ℝ`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The coordinates of `E4` are continuous. -/
theorem continuous_coord4 (i : Fin 4) : Continuous (fun q : E4 => q i) :=
  PiLp.continuous_apply 2 _ i

/-- **The Cartesian radius `r(q) = √(q₀² + q₁²)` of the core coordinates is continuous.**
(Only the first two of the four coordinates enter.) -/
theorem continuous_sqrt_sq_add_sq :
    Continuous (fun q : E4 => Real.sqrt (q 0 ^ 2 + q 1 ^ 2)) :=
  Real.continuous_sqrt.comp
    (((continuous_coord4 0).pow 2).add ((continuous_coord4 1).pow 2))

/-- **The requested statement: the core box is open.** -/
theorem isOpen_coreBox : IsOpen coreBox := by
  simpa [coreBox] using isOpen_lt continuous_sqrt_sq_add_sq continuous_const

end Work.Cusp

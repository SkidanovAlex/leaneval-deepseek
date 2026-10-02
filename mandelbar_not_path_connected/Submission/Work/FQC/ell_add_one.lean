/-
# `ell t (w + 1) = ell t w + 1`

The MNS twist `ell t w = w + i · t · saw (w.re)` of the Écalle cylinder commutes with the
shift `w ↦ w + 1`.  The real part of `w + 1` is `w.re + 1`, and the triangle wave `saw` is
`1`-periodic (`saw_add_one`), so the vertical shear is unchanged; both sides then reduce to
`w + 1 + i·t·saw w.re`.
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.saw_add_half
import Submission.Work.FQC.saw_add_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

noncomputable section

namespace Work.FQC

theorem ell_add_one (t : ℝ) (w : ℂ) : Work.FQC.ell t (w + 1) = Work.FQC.ell t w + 1 := by
  rw [ell_apply, ell_apply, Complex.add_re, Complex.one_re, saw_add_one]
  ring

end Work.FQC

end

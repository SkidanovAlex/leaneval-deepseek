import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.rayPt_add_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- The rays of the dynamical plane depend on the angle only modulo `ℤ`: landing of the ray of
angle `θ + k` at `y` is the same as landing of the ray of angle `θ` at `y`, for every `k : ℤ`.
This is immediate from `rayPt_add_int`: the two families of ray points are literally equal. -/
theorem landsN_add_int {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) (k : ℤ) (y : ℂ) :
    (Work.EL.LandsN hN (θ + k) y ↔ Work.EL.LandsN hN θ y) := by
  have hl : (fun t : ℝ => Work.EL.rayPt hN (θ + k) t) = fun t : ℝ => Work.EL.rayPt hN θ t :=
    funext fun t => Work.ELTop.rayPt_add_int hN θ t k
  constructor <;> intro h <;> simpa only [Work.EL.LandsN, hl] using h

end Work.ELAssembly

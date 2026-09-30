import Mathlib
import Submission.Work.Charts.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Charts

universe u

open CategoryTheory in
theorem eq_divOf_of_linEquiv_of_landsIn {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} [Work.SpecLin.DivBase C] {R : Work.Charts.RochData C}
    [Work.SpecLin.SymGeom C R.g] {F : Type u} [Field F] [Algebra K F]
    {d : Work.Charts.BNData C R} (y : Work.GCBasics.FPt (Work.Charts.Sym C R.g) F)
    (hy : Work.GCBasics.RPt.LandsIn y d.V) {D : Work.GCBasics.Dv C F}
    (hD : D.IsEffective) (hdeg : Work.GCBasics.Ddeg C F D = (R.g : ℤ))
    (he : Work.GCBasics.LinEquiv C (Work.Charts.divOf y) D) :
    D = Work.Charts.divOf y ∧ Work.GCBasics.ell C D = 1 := by
  -- the point of the Brill--Noether chart has `ℓ = 1`
  have hy1 : Work.GCBasics.ell C (Work.Charts.divOf y) = 1 := d.ell_eq_one_of_landsIn y hy
  -- `ℓ` only depends on the linear equivalence class
  have hD1 : Work.GCBasics.ell C D = 1 := by
    rw [← Work.GCBasics.ell_eq_of_linEquiv he]
    exact hy1
  -- an effective divisor of degree `g` with `ℓ = 1` is the unique effective divisor
  -- in its class, so `D` recovers `divOf y`
  exact ⟨R.eq_of_ell_eq_one hD (Work.SpecLin.SymGeom.divOf_isEffective y) hdeg hD1
    (Work.GCBasics.LinEquiv.symm he), hD1⟩

end Work.Charts

import Mathlib
import Submission.Work.Charts.ChartCg
import Submission.Work.Charts.mem_bnOpen_perm
import Submission.Work.Charts.exists_perm_of_quotMap_eq
import Submission.Work.SymQuot.Prod.isReduced_pi_prod
import Submission.Work.SymQuot.Sym.isIntegral_sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

theorem chartOpen_ne_bot {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {n : ℕ} [Work.SpecLin.SymGeom C n] (U : C.left.Opens)
    (s : Fin n → (C.left.presheaf.obj (Opposite.op U)))
    (hclosed : IsClosedMap (Work.Charts.quotMap C n).left.base)
    (hδ : Work.Charts.bnDelta C U n s ≠ 0) :
    Work.Charts.chartOpen C n U s hclosed ≠ ⊥ := by
  -- `C^n` is reduced, being a power of a geometrically reduced curve
  haveI : Smooth C.toOver.hom := C.smooth.smooth
  haveI : IsReduced (Cprod C n).left := Work.SymQuot.Prod.isReduced_pi_prod C.toOver n
  -- hence `δ ≠ 0` means `D(δ) ⊆ C^n` is a nonempty open
  have hbn : bnOpen C U n s ≠ ⊥ := by
    intro h
    exact hδ ((AlgebraicGeometry.basicOpen_eq_bot_iff (bnDelta C U n s)).mp h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty (bnOpen C U n s)).mp hbn
  -- a point of `D(δ)` has all its preimages in `D(δ)`, since they are its permutations
  intro hbot
  have hy : (quotMap C n).left x ∈ chartOpen C n U s hclosed := by
    rw [mem_chartOpen]
    intro x' hx'
    obtain ⟨σ, hσ⟩ := exists_perm_of_quotMap_eq n hx'.symm
    rw [← hσ]
    exact (mem_bnOpen_perm U s σ).mp hx
  rw [hbot] at hy
  exact hy

end Work.Charts

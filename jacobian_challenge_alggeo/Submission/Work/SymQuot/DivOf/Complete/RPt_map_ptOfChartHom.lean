import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.RhoData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
theorem RPt_map_ptOfChartHom {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F F' : Type u} [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F') {V : C.left.Opens} (hV : IsAffineOpen V)
    (Φ : ↥(Work.SymQuot.chartInvariants (C := C) (n := n)
        (Work.SymQuot.piOpen C.toOver V n) (Work.SymQuot.DivOf.symPiOpen_invariant C n V)) →+* F)
    (hΦ : ∀ k : K, Φ (Work.SymQuot.DivOf.chartConst C n
      (Work.SymQuot.DivOf.Complete.chartOf C n hV) k) = algebraMap K F k)
    (hΦ' : ∀ k : K, (e.toRingHom.comp Φ) (Work.SymQuot.DivOf.chartConst C n
      (Work.SymQuot.DivOf.Complete.chartOf C n hV) k) = algebraMap K F' k) :
    Work.SpecLin.RPt.map e (Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV Φ hΦ) =
      Work.SymQuot.DivOf.Complete.ptOfChartHom C n hV (e.toRingHom.comp Φ) hΦ' := by
  apply Over.OverMorphism.ext
  simp only [Work.SpecLin.RPt.map, Work.SymQuot.DivOf.Complete.ptOfChartHom,
    Over.homMk_left, Over.comp_left, Work.SpecLin.specOfMap, Work.SpecLin.specOfMapHom]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end Work.SymQuot.DivOf.Complete

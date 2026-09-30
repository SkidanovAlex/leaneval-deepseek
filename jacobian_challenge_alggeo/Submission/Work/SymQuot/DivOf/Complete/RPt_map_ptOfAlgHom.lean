import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
theorem RPt_map_ptOfAlgHom {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {V : C.left.Opens} (hV : IsAffineOpen V) {S S' : Type u} [CommRing S] [Algebra K S]
    [CommRing S'] [Algebra K S'] (f : S →ₐ[K] S') (κ : Γ(C.left, V) →ₐ[K] S) :
    Work.SpecLin.RPt.map f (ptOfAlgHom C hV κ) = ptOfAlgHom C hV (f.comp κ) := by
  apply Over.OverMorphism.ext
  simp only [Work.SpecLin.RPt.map, ptOfAlgHom, Over.homMk_left, Over.comp_left,
    Category.assoc, Work.SpecLin.specOfMap_comp]

end Work.SymQuot.DivOf.Complete

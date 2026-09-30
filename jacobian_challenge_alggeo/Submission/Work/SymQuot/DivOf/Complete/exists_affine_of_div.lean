import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
theorem exists_affine_of_div {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] (D : Work.SpecLin.Dv C F) :
    ∃ V : C.left.Opens, IsAffineOpen V ∧ Nonempty V ∧
      ∀ z ∈ D.support, z.point ∈ C.bcOpens F V := by
  classical
  haveI : Work.SymQuot.CurveAffineCover C := Work.SymQuot.instCurveAffineCover C
  have hSfin : (((fun z : (C.baseChange F).Place => C.baseChangeFst F z.point) ''
        (↑D.support : Set (C.baseChange F).Place)) ∪ {genericPoint C.left} : Set C.left).Finite :=
    (D.support.finite_toSet.image _).union (Set.finite_singleton _)
  obtain ⟨V, hVaff, hVsub⟩ :=
    Work.SymQuot.CurveAffineCover.exists_isAffineOpen_superset (C := C) _ hSfin
  refine ⟨V, hVaff, ?_, ?_⟩
  · exact ⟨genericPoint C.left, hVsub (Set.mem_union_right _ (Set.mem_singleton _))⟩
  · intro z hz
    exact hVsub (Set.mem_union_left _ ⟨z, hz, rfl⟩)

end Work.SymQuot.DivOf.Complete

import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ThreeConnected.Excision

theorem isZero_homology_three_of_isIso_homology_one
    (S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℤ) ℕ))
    (hS : S.ShortExact) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ j, CategoryTheory.IsIso (HomologicalComplex.homologyMap S.f j)) :
    CategoryTheory.Limits.IsZero (S.X₃.homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  haveI := h n
  exact hS.exactAt_X₃ n (by infer_instance)
    (fun j _ => by haveI := h j; infer_instance)

end Work.ThreeConnected.Excision

import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

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

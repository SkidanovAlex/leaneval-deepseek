import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.Cre_ann_adjoint
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

theorem CreOf_annOf_adjoint {m : ℕ} (f : Fin m → ℝ) (p q : Work.BoseB4.RealFock m) :
    Work.BoseB4.bomb m (Work.BoseB4.creOf m f p) q
      = Work.BoseB4.bomb m p (Work.BoseB4.annOf m f q) := by
  -- `creOf`/`annOf` are finite sums of single-mode operators, and `bomb` is
  -- bilinear, so both sides reduce to the sum of the single-mode adjointness
  -- identities `Cre_ann_adjoint`.
  simp only [creOf, annOf, LinearMap.sum_apply, map_sum, map_smul, LinearMap.smul_apply]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Cre_ann_adjoint]

end Work.BoseB4

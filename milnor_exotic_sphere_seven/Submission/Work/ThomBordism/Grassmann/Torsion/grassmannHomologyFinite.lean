import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.ThomBordism.existsFiniteGoodCover_of_c2Atlas
import Submission.Work.ThomBordism.finiteGoodCoverHomology
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.ChartFrame
import Submission.Work.ThomBordism.Grassmann.Smooth.BasicDefs
import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Model
import Submission.Work.ThomBordism.compactHomologyFinite

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann.Torsion

open scoped Manifold

theorem grassmannHomologyFinite (k m n : ℕ) : Module.Finite ℤ
    ((Work.Cohomology.chainC ℤ
      (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.OG k m))).homology n) := by
  exact Work.ThomBordism.compactHomologyFinite (n := k * m) (k := n)
    (X := Work.ThomBordism.Grassmann.OG k m)

end Work.ThomBordism.Grassmann.Torsion

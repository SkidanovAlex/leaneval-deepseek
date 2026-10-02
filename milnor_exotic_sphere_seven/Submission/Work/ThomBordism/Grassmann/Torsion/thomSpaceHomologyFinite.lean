import Mathlib
import Submission.Work.ThomBordism.finiteGoodCoverHomology
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.ThomBordism.moduleFiniteHomologyBiprod
import Submission.Work.ThomBordism.Grassmann.OpenQuotient
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom
import Submission.Work.ThomBordism.Grassmann.Torsion.contractibleFar
import Submission.Work.ThomBordism.Grassmann.Torsion.RadialDefs
import Submission.Work.ThomBordism.Grassmann.Frame
import Submission.Work.ThomBordism.Grassmann.Rotation
import Submission.Work.ThomBordism.Grassmann.ChartFrame
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.existsFiniteGoodCover_of_c2Atlas
import Submission.Work.ThomBordism.compactHomologyFinite
import Submission.Work.ThomBordism.Grassmann.Torsion.thomSpaceReduction
import Submission.Work.ThomBordism.Grassmann.Torsion.grassmannHomologyFinite
import Submission.Work.ThomBordism.Grassmann.Torsion.annulusFiniteness

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann.Torsion

theorem thomSpaceHomologyFinite (k m n : ℕ) : Module.Finite ℤ
    ((Work.Cohomology.chainC ℤ
      (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.TautologicalThomSpace k m))).homology n) := by
  have hG : ∀ j, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.ThomBordism.Grassmann.OG k m))).homology j) :=
    fun j => Work.ThomBordism.Grassmann.Torsion.grassmannHomologyFinite k m j
  have hU : ∀ j, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(Work.ThomBordism.Grassmann.Torsion.near k m 2))).homology j) :=
    fun j => Work.ThomBordism.Grassmann.Torsion.moduleFinite_homology_of_homeomorph
      (Work.ThomBordism.Grassmann.Torsion.homeoNear k m 2) j
      (Work.ThomBordism.Grassmann.Torsion.moduleFinite_homology_of_disc k m j (hG j))
  have hK : ∀ j, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(Work.ThomBordism.Grassmann.Torsion.annSet k m))).homology j) :=
    fun j => Work.ThomBordism.Grassmann.Torsion.annSetHomologyFinite k m j
  exact Work.ThomBordism.Grassmann.Torsion.thomSpaceHomologyFinite_of_inputs k m hU hK n

end Work.ThomBordism.Grassmann.Torsion

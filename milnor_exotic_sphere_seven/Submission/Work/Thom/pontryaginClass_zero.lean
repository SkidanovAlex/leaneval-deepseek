import Mathlib
import Submission.Work.Thom.manifoldP1
import Submission.Work.Thom.chernClass_zero_eq_oneH
import Submission.Work.Thom.pontryaginClass_one

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

theorem pontryaginClass_zero {k : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    Work.Thom.pontryaginClass 0 Z = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)) := by
  -- `p_0(E) = (-1)^0 • c_0(E ⊗_ℝ ℂ) = c_0(E ⊗_ℝ ℂ)`, the degree transport being invisible.
  unfold Work.Thom.pontryaginClass
  rw [pow_zero, one_zsmul]
  change Work.Thom.cohTransport (show (0 : ℕ) = 0 from (by ring : 2 * (2 * 0) = 4 * 0))
    (chernClass k 0 (complexificationCore Z)) =
    Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B))
  rw [cohTransport_self]
  exact chernClass_zero_eq_oneH (complexificationCore Z)

end Work.Thom

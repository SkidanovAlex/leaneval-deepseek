import Mathlib
import Submission.Work.Thom.CapGeomDefs
import Submission.Work.Cohomology.sphereCapContractible
import Submission.Work.Cohomology.SphDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The open cap `{last > -1/2}` of the unit sphere is contractible

The open cap `flGt n (-(1/2)) = {v : S^{n+1} | -(1/2) < lastC n v}` of the unit sphere of
`ℝ^{n+1}` contains the north pole `(0, ..., 0, 1)`.  Under stereographic projection from the south
pole `(0, ..., 0, -1)` it is the complement of a closed cap, hence homeomorphic to an open ball
(`tgtSet`), which is convex and non-empty, hence contractible
(`Work.Cohomology.sphereCapContractible`).

The statement of `sphereCapContractible` concerns the *flat* subtype
`{x : ℝ^{n+1} // ‖x‖ = 1 ∧ x (Fin.last n) > -1/2}`, whereas `↥(flGt n (-(1/2)))` is the nested
subtype `{v : {x : ℝ^{n+1} // ‖x‖ = 1} // ...}`; the two are canonically homeomorphic
(`Work.Cohomology.flatHomeo`).  We transfer contractibility along this homeomorphism.
-/

set_option linter.style.haveILetI false

namespace Work.Thom.CapContract

open Work.Thom

noncomputable section

/-- The open cap `{x : S^{n+1} | -(1/2) < lastC n x}` of the unit sphere is contractible. -/
theorem contractibleSpace_flGt (n : ℕ) : ContractibleSpace ↥(flGt n (-(1 / 2))) := by
  haveI h : ContractibleSpace
      {x : EuclideanSpace ℝ (Fin (n + 1)) // mSph (n + 1) x ∧ -(1 / 2) < lastC n x} :=
    Work.Cohomology.sphereCapContractible n (1 / 2) (by norm_num) (by norm_num)
  exact Homeomorph.contractibleSpace
    (Work.Cohomology.flatHomeo (q := mSph (n + 1)) (P := fun x => -(1 / 2) < lastC n x))

end

end Work.Thom.CapContract

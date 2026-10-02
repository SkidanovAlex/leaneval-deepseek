import Mathlib
import Submission.Work.Projective.Cover
import Submission.Work.Cohomology.contractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomology of the affine charts of `ℂPⁿ` (the pieces of the Mayer–Vietoris cover)

Each affine chart of `ℂPⁿ` is homeomorphic to `ℂⁿ` (`Work.Projective.chartHomeomorph`), hence
contractible, hence has vanishing positive-degree singular cohomology:
`Work.Projective.isZero_chartSet_cohomology`, and in the form in which the Mayer–Vietoris
machinery of `Submission/Work/Cohomology/` consumes it, `Work.Projective.isZero_cochainU_cp2`.
-/

open scoped Topology
open CategoryTheory

namespace Work.Projective

open Work.Cohomology

noncomputable section

/-- **The positive-degree cohomology of an affine chart of `ℂPⁿ` vanishes** (charts are
contractible). -/
theorem isZero_chartSet_cohomology (n : ℕ) (i : Fin (n + 1)) (k : ℕ) :
    CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ (k + 1) (TopCat.of ↥(chartSet i))) :=
  contractible ℤ (TopCat.of ↥(chartSet i)) k

/-- The `U`-part of the Mayer–Vietoris cover of `ℂP²` has vanishing positive-degree cohomology. -/
theorem isZero_cochainU_cp2 (k : ℕ) :
    CategoryTheory.Limits.IsZero ((cochainU cp2U cp2V).homology (k + 1)) := by
  haveI : ContractibleSpace ↥cp2U := contractibleSpace_chartSet 2 0
  exact contractible ℤ (TopCat.of ↥cp2U) k

end

end Work.Projective

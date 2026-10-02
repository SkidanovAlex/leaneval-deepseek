import Submission.Work.SphHomology.Defs
import Submission.Work.SphHomology.sphPiece_homeo
import Submission.Work.SphHomology.sphPiece_charted_prod

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The trivialised piece of the sphere bundle is a charted space

Combining the identification `SphPiece Z i ≃ₜ ↥(Z.baseSet i) × S^{k-1}` with the charted structure
of the product gives a charted space structure on the piece of the sphere bundle over a trivialising
set, modelled on `ℝ^{8 + (k-1)}`.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.SphHomology

noncomputable section

/-- **The piece of the sphere bundle over a trivialising set is a charted space** of model dimension
`8 + (k-1)`. -/
theorem sphPiece_charted {B : Type*} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {k : ℕ} (hk : 1 ≤ k) {ι : Type*}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z) (i : ι) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin (8 + (k - 1)))) (SphPiece Z i)) := by
  obtain ⟨e⟩ := sphPiece_homeo Z hZ i
  obtain ⟨c⟩ := sphPiece_charted_prod (Z := Z) hk i
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + (k - 1))))
      (↥(Z.baseSet i) × ModelSph (EuclideanSpace ℝ (Fin k))) := c
  exact ⟨Homeomorph.chartedSpace e⟩

end

end Work.SphHomology

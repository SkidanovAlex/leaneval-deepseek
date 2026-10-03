import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Descent.DiagAct

set_option maxHeartbeats 1000000

namespace Work.ORTorsion.Descent

open scoped TensorProduct
open Work.ORTorsion

/-- On `V ⊗[K] ↥(L.D ⊤)`, the diagonal action `diagAct L H ↥(L.D ⊤)` of `K[H]` (through the
identification `↥(L.D H) ↪ ↥(L.D ⊤)`, i.e. `instModuleDHtop`) coincides with the diagonal action
`instDiagTopSmul` of `K[G]` composed with `mapToG H : K[H] → K[G]`. -/
theorem diagAct_eq_instDiagTop {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (H : Subgroup G) :
    ∀ (x : MonoidAlgebra K H) (m : V ⊗[K] ↥(L.D ⊤)), diagAct L H ↥(L.D ⊤) x m
      = mapToG H x • m := by
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => intro m; simp
  | add p q hp hq =>
      intro m
      simp only [map_add, LinearMap.add_apply, hp m, hq m, TorsionData.instDiagTopSmul_apply]
  | single h c =>
      intro m
      have hsingle : diagAct L H ↥(L.D ⊤) (MonoidAlgebra.single h c)
          = c • (diagActGroup L H ↥(L.D ⊤) h : Module.End K (V ⊗[K] ↥(L.D ⊤))) := by
        show (MonoidAlgebra.lift K (Module.End K (V ⊗[K] ↥(L.D ⊤))) H
            (diagActGroup L H ↥(L.D ⊤))) (MonoidAlgebra.single h c) = _
        rw [MonoidAlgebra.lift_single]
      have hmap : mapToG H (MonoidAlgebra.single h c) = MonoidAlgebra.single (h : G) c := by
        rw [mapToG, MonoidAlgebra.lift_single]
        simp [MonoidAlgebra.smul_single]
      rw [TorsionData.instDiagTopSmul_apply, hsingle, hmap, diagRingHom_single_coeff,
        LinearMap.smul_apply, LinearMap.smul_apply]
      congr 1

end Work.ORTorsion.Descent

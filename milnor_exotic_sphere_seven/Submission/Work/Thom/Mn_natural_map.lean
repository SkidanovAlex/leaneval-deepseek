import Mathlib
import Submission.Work.Thom.ProdMapTools
import Submission.Work.Thom.step_natural_map
import Submission.Work.Thom.Mn_natural_map_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

theorem Mn_natural_map (n : ℕ) {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) :
    (Work.Thom.relCohMap (Work.Thom.prodMapA g (EuclideanSpace ℝ (Fin n)))
      (Work.Thom.Sph B' n) (Work.Thom.Sph B n) (fun _ h => h) ℤ n).hom (Work.Thom.Mn n B)
      = Work.Thom.Mn n B' := by
  induction n with
  | zero => exact Mn_natural_map_zero g
  | succ m ih =>
      show (relCohMap (prodMapA g (EuclideanSpace ℝ (Fin (m+1)))) (Sph B' (m+1))
              (Sph B (m+1)) (fun _ h => h) ℤ (m+1)).hom (step B m (Mn m B))
            = step B' m (Mn m B')
      rw [step_natural_map g m (Mn m B), ih]

end Work.Thom

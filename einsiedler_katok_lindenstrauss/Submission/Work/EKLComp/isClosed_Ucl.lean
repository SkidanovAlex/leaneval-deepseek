import Mathlib
import Submission.Work.EKLComp.LeafDefs

/-!
# `Work.EKLComp.isClosed_Ucl`

The closed sup-metric ball `Ucl U r` around the identity inside a subgroup `U ≤ SL₃(ℝ)` is
closed as soon as `U` is: `Ucl U r` is the intersection of the closed subgroup `U` with the
finitely many closed entry conditions `|g_{ij} - δ_{ij}| ≤ r`, each of which is the preimage of
a closed set under a continuous function.
-/

namespace Work.EKLComp

open Work.EKLContract

theorem isClosed_Ucl (U : Subgroup Work.EKLContract.SL3) (hcl : IsClosed (U : Set Work.EKLContract.SL3))
    (r : ℝ) : IsClosed (Work.EKLComp.Ucl U r) := by
  have hset : Ucl U r = (U : Set SL3) ∩
      {g : SL3 | ∀ i j : Fin 3,
        |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r} := by
    ext g
    simp only [Ucl, Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact Iff.rfl
  rw [hset]
  refine IsClosed.inter hcl ?_
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  refine isClosed_le ?_ continuous_const
  exact (((continuous_apply j).comp
    (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)).sub
      continuous_const).abs

end Work.EKLComp

import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map

namespace Work.ORCoherence.Tensor

open scoped TensorProduct

theorem balanced_span_tmul_one_eq_top {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule.span S (Set.range (fun m : M => Balanced.tmul f 1 m)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        rw [Submodule.Quotient.mk_add]
        exact add_mem ha hb
    | tmul s m =>
        show Balanced.tmul f s m ∈ Submodule.span S (Set.range fun m => Balanced.tmul f 1 m)
        have h : Balanced.tmul f s m = s • Balanced.tmul f 1 m := by
          rw [Balanced.smul_tmul, mul_one]
        rw [h]
        exact Submodule.smul_mem _ s (Submodule.subset_span ⟨m, rfl⟩)

end Work.ORCoherence.Tensor

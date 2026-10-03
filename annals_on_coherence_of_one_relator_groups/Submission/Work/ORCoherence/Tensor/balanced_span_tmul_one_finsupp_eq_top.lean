import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map

namespace Work.ORCoherence.Tensor

open scoped TensorProduct

theorem balanced_span_tmul_one_finsupp_eq_top {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (X : Type*) :
    Submodule.span S (Set.range (fun i : X => Balanced.tmul f 1 (Finsupp.single i (1 : R)))) = ⊤ := by
  let T : Submodule S (Balanced f (X →₀ R)) :=
    Submodule.span S (Set.range (fun i : X => Balanced.tmul f 1 (Finsupp.single i (1 : R))))
  change T = ⊤
  have hsingle : ∀ (a : X) (b : R),
      Balanced.tmul f 1 (Finsupp.single a b) = (f b) • Balanced.tmul f 1 (Finsupp.single a (1 : R)) := by
    intro a b
    rw [← Finsupp.smul_single_one a b, ← Balanced.tmul_smul f 1 b, one_mul]
    simpa using (Balanced.smul_tmul f (f b) 1 (Finsupp.single a (1 : R))).symm
  have hgen : ∀ m : X →₀ R, Balanced.tmul f 1 m ∈ T := by
    intro m
    induction m using Finsupp.induction_linear with
    | zero => rw [Balanced.tmul_zero]; exact T.zero_mem
    | add f' g hf' hg =>
        rw [Balanced.tmul_add]
        exact T.add_mem hf' hg
    | single a b =>
        rw [hsingle a b]
        exact T.smul_mem (f b) (Submodule.subset_span ⟨a, rfl⟩)
  rw [Submodule.eq_top_iff']
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    suffices hs : y ∈ T.comap (Submodule.mkQ (balancedRel f (X →₀ R))) by
      exact Submodule.mem_comap.mp hs
    have htop : T.comap (Submodule.mkQ (balancedRel f (X →₀ R))) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro z
      rw [Submodule.mem_comap]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s m =>
          show Balanced.tmul f s m ∈ T
          have h2 : Balanced.tmul f s m = s • Balanced.tmul f 1 m := by
            rw [Balanced.smul_tmul, mul_one]
          rw [h2]
          exact T.smul_mem s (hgen m)
      | add p q hp hq => exact T.add_mem hp hq
    rw [htop]
    exact Submodule.mem_top

end Work.ORCoherence.Tensor

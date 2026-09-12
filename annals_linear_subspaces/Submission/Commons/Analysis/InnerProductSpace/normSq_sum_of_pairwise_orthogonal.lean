import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.InnerProductSpace

lemma normSq_sum_of_pairwise_orthogonal {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : ι → E)
    (horth : Pairwise fun i j => inner ℝ (z i) (z j) = 0) :
    ‖(Finset.univ.sum fun i => z i)‖ ^ 2 = Finset.univ.sum (fun i => ‖z i‖ ^ 2) := by
  calc
    ‖(Finset.univ.sum fun i => z i)‖ ^ 2
        = inner ℝ (Finset.univ.sum fun i => z i) (Finset.univ.sum fun i => z i) := by
          rw [real_inner_self_eq_norm_sq]
    _ = Finset.univ.sum (fun i => inner ℝ (z i) (Finset.univ.sum fun j => z j)) := by
          rw [sum_inner]
    _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j => inner ℝ (z i) (z j))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [inner_sum]
    _ = Finset.univ.sum (fun i => inner ℝ (z i) (z i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by
            intro j hj hij
            exact horth hij.symm)
    _ = Finset.univ.sum (fun i => ‖z i‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [real_inner_self_eq_norm_sq]

end Commons.Analysis.InnerProductSpace
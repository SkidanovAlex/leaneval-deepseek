import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Analysis.InfiniteSum.summable_prod_mul

namespace Commons.Analysis.InfiniteSum

theorem tsum_prod_mul_of_nonneg {ι κ : Type*} {a : ι → ℝ} {b : κ → ℝ}
    (ha : Summable a) (hb : Summable b) (hna : ∀ i, 0 ≤ a i) (hnb : ∀ j, 0 ≤ b j) :
    ∑' p : ι × κ, a p.1 * b p.2 = (∑' i, a i) * (∑' j, b j) := by
  have hf : Summable (fun p : ι × κ => a p.1 * b p.2) := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (hna p.1) (hnb p.2))]
    refine ⟨fun x => ?_, ?_⟩
    · exact hb.mul_left (a x)
    · have h : (fun x => ∑' y, a x * b y) = fun x => a x * (∑' y, b y) := by
        funext x
        rw [tsum_mul_left]
      rw [h]
      exact ha.mul_right _
  exact (Summable.tsum_mul_tsum ha hb hf).symm

end Commons.Analysis.InfiniteSum
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

namespace Work.ORVonNeumann.Rep

/-- `matOp` is multiplicative: the operator attached to a product of matrices over `N(G)` is the
composite of the operators attached to the factors. This is the matrix amplification of the
fact that the multiplication on `B(ℓ²(G))` is composition, together with `hcoord_matOp`. -/
theorem vnMatOpMul {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) (B : Matrix (Fin m) (Fin k) (↥(Work.ORVonNeumann.groupVonNeumann G))) : Work.ORVonNeumann.Rep.matOp (G := G) (A * B) = (Work.ORVonNeumann.Rep.matOp (G := G) A).comp (Work.ORVonNeumann.Rep.matOp (G := G) B) := by
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro i
  rw [hcoord_apply, ContinuousLinearMap.comp_apply, hcoord_apply]
  simp only [matOp_apply]
  -- Compare the `i`-th coordinates: the right hand side is
  -- `∑ j, A i j (∑ k, B j k (x k))`, and the left hand side is `∑ k, (A * B) i k (x k)`.
  have h1 : ∀ j : Fin m, (A i j : boundedEnd G) (∑ k : Fin k, (B j k : boundedEnd G) (x.ofLp k))
      = ∑ k : Fin k, ((A i j : boundedEnd G) * (B j k : boundedEnd G)) (x.ofLp k) := by
    intro j
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← sum_apply]
  have hco : ((A * B) i k : boundedEnd G)
      = ∑ j : Fin m, (A i j : boundedEnd G) * (B j k : boundedEnd G) := by
    rw [Matrix.mul_apply]
    push_cast
    rfl
  rw [hco]

end Work.ORVonNeumann.Rep

import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.SliceDefs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The fibrewise mean of an indicator is the probability of the corresponding event in the
uniform colouring of `↥A`. -/
theorem fibreMean_indicator {k : ℕ} [Nonempty (V → Fin k)] (A : Finset V)
    [Nonempty (↥A → Fin k)] (E : Set (V → Fin k)) (f : V → Fin k) :
    fibreMean A (fun f' : V → Fin k => E.indicator (fun _ => (1 : ℝ)) f') f
      = (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | graft A g f ∈ E} := by
  classical
  have hcard : Fintype.card (↥A → Fin k) = k ^ A.card := by
    rw [card_colSpace, Fintype.card_coe]
  have hmass : (colSpace (V := ↥A) k).mass = fun _ => (((k : ℝ) ^ A.card))⁻¹ := by
    rw [colSpace_mass, hcard, Nat.cast_pow]
  rw [fibreMean, FinSpace.prob, hmass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : graft A g f ∈ E
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show g ∈ {g : ↥A → Fin k | graft A g f ∈ E}
        from h)]
    ring
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show g ∉ {g : ↥A → Fin k | graft A g f ∈ E} from h)]
    ring

end Work.Deep.Sparse

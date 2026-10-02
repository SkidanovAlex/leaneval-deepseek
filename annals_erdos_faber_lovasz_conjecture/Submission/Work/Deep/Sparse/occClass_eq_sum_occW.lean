import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.occHtrunc_eq_sum

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Sparse

/-!
# The two readings of the truncated occupancy statistic coincide

`occClass G f v J = ∑_c occHtrunc J (colourClassCount G f v c)` reads the truncated
class statistic of the naive colouring procedure through the colour classes of `v`,
while

`occSlice G f v J = ∑_{2 ≤ j ≤ J} occW j · #{c : j ≤ colourClassCount G f v c}`

reads it through the occupancy numbers of the slices `j ≤ colourClassCount`.

By `occHtrunc_eq_sum` (of `Submission/Work/Deep/Sparse/occHtrunc_eq_sum.lean`) each
class contribution is the cutoff partial sum of its increments,

`occHtrunc J n = ∑_{2 ≤ j ≤ J} occW j · [j ≤ n]`.

Summing this over the colours `c` and interchanging the two finite sums turns the
sum of indicators over the colours into the occupancy number of the `j`-th slice,

`∑_c [j ≤ colourClassCount G f v c] = #{c : j ≤ colourClassCount G f v c}`,

which is exactly the `occSlice` reading.
-/

theorem occClass_eq_sum_occW {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k)
    (v : V) (J : ℕ) : occClass G f v J = occSlice G f v J := by
  -- The occupancy number of the `j`-th slice, written as a sum of indicators.
  have hcard : ∀ j : ℕ, ∑ c : Fin k, (if j ≤ colourClassCount G f v c then (1 : ℝ) else 0)
      = (((Finset.univ : Finset (Fin k)).filter
          (fun c => j ≤ colourClassCount G f v c)).card : ℝ) := by
    intro j
    rw [← Finset.sum_filter, Finset.sum_const, Nat.smul_one_eq_cast]
  calc occClass G f v J
      = ∑ c : Fin k, ∑ j ∈ Finset.Icc 2 J,
          occW j * (if j ≤ colourClassCount G f v c then (1 : ℝ) else 0) := by
        simp only [occClass, occHtrunc_eq_sum]
    _ = ∑ j ∈ Finset.Icc 2 J, ∑ c : Fin k,
          occW j * (if j ≤ colourClassCount G f v c then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.Icc 2 J, occW j *
          ∑ c : Fin k, (if j ≤ colourClassCount G f v c then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = occSlice G f v J := by
        simp only [occSlice]
        exact Finset.sum_congr rfl fun j _ => by rw [hcard j]

end Work.Deep.Sparse

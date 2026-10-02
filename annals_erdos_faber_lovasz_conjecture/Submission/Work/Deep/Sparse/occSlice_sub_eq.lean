import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ncpTailDefs
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbModel

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Sparse

theorem occSlice_sub_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k D : ℕ} (hD : ncpJ ≤ D) (f : V → Fin k) (v : V) :
    occSlice G f v D - occSlice G f v ncpJ
      = ∑ j ∈ Finset.Icc (ncpJ + 1) D, occW j * (ncpN G f v j : ℝ) := by
  have h18 : ncpJ = 18 := rfl
  have hsplit : Finset.Icc 2 ncpJ ∪ Finset.Icc (ncpJ + 1) D = Finset.Icc 2 D := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 2 ncpJ) (Finset.Icc (ncpJ + 1) D) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'
    omega
  simp only [occSlice]
  rw [← hsplit, Finset.sum_union hdisj, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun j _ => rfl

end Work.Deep.Sparse

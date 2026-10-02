/-
# The first-moment bound for the unretained occupancy count

For the uniform colouring `f : V → Fin k` of `V` (`colSpace`,
`Submission/Work/Deep/Sparse/ProbBasic.lean`), a finite vertex set `A ⊆ V` and a `j ≥ 1`,
the expected number of colours occurring at least `j` times on `A` is at most

  `k * ((|A| / k)^j / j!)`.

This is the standard first-moment bound obtained by writing `occRaw A f j` as the sum, over
the `k` colours, of the indicator that a fixed colour occurs at least `j` times on `A`, and
bounding each of these indicators by a union bound over the `j`-subsets of `A`.

The proof is assembled from two previously proved ingredients.

* `Work.Deep.Sparse.fibreMean_occRaw_le` bounds the *fibre mean* — the average of
  `occRaw A · j` over all recolourings of the `A`-coordinates of a fixed colouring `f` — by
  `k * ((|A|/k)^j / j!)`.  There the union bound is carried out on the smaller sample space
  `↥A → Fin k` (via `fibreMean`, `Submission/Work/Deep/Sparse/SliceDefs.lean`).
* `Work.Deep.Sparse.colSpace_expect_fibreMean` is the tower property of the fibre mean: the
  expectation of `fibreMean A Y` under the uniform colouring `V → Fin k` equals the
  expectation of `Y`.  Since `occRaw A · j` depends only on the colours of the vertices of
  `A`, averaging the fibrewise first-moment bound over the colours outside `A` therefore
  yields the unconditional bound.

The degenerate case `k = 0` (where every `Fin 0`-valued function is colouring-free and both
sides vanish) is handled inside `fibreMean_occRaw_le`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.SliceDefs
import Submission.Work.Deep.Sparse.fibreMean_occRaw_le
import Submission.Work.Deep.Sparse.colSpace_expect_fibreMean

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem expect_occRaw_le {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (V → Fin k)] (A : Finset V) {j : ℕ} (hj : 0 < j) :
    (colSpace (V := V) k).expect (fun f => (occRaw A f j : ℝ))
      ≤ (k : ℝ) * (((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ)) := by
  classical
  -- The unconditional mean of `occRaw A · j` is the average of its fibre means.
  have hbridge : (colSpace (V := V) k).expect (fun f : V → Fin k => (occRaw A f j : ℝ))
      = (colSpace (V := V) k).expect
          (fun f : V → Fin k => fibreMean A (fun f' : V → Fin k => (occRaw A f' j : ℝ)) f) :=
    (colSpace_expect_fibreMean (V := V) (k := k) A
      (fun f' : V → Fin k => (occRaw A f' j : ℝ))).symm
  calc (colSpace (V := V) k).expect (fun f : V → Fin k => (occRaw A f j : ℝ))
      = (colSpace (V := V) k).expect
          (fun f : V → Fin k => fibreMean A (fun f' : V → Fin k => (occRaw A f' j : ℝ)) f) :=
        hbridge
    _ ≤ (colSpace (V := V) k).expect
          (fun _ : V → Fin k =>
            (k : ℝ) * (((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ))) :=
        FinSpace.expect_mono _ fun f => fibreMean_occRaw_le A hj f
    _ = (k : ℝ) * (((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ)) :=
        FinSpace.expect_const _ _

end Work.Deep.Sparse

import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.occH_eq_sum_occW

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Sparse

/-!
# The truncated class contribution as a cutoff partial sum of its increments

`occHtrunc J n = occH (min n J)` (of `Submission/Work/Deep/Sparse/NcpDefs.lean`)
truncates the class contribution `occH n = C(n,2) - C(n,3)` at level `J`.
By the telescoping identity `occH_eq_sum_occW`, `occH m` is the sum of the
increments `occW j = occH j - occH (j-1)` over `2 ≤ j ≤ m`, so truncating at
`J` while capping the class size at `n` keeps exactly those increments with
`2 ≤ j ≤ J` and `j ≤ n`:

  `occHtrunc J n = ∑_{2 ≤ j ≤ J} occW j · [j ≤ n]`.

This is the single-class instance of the identity `occClass = occSlice`
between the two readings of the truncated occupancy statistic.
-/

theorem occHtrunc_eq_sum (J n : ℕ) :
    occHtrunc J n = ∑ j ∈ Finset.Icc 2 J, occW j * (if j ≤ n then (1 : ℝ) else 0) := by
  -- The cutoff `{j ∈ Icc 2 J : j ≤ n}` is `Icc 2 (min n J)`: it cuts `Icc 2 J`
  -- back to `Icc 2 n` when `n < J`, and leaves it unchanged when `J ≤ n`.
  have hfilter : (Finset.Icc 2 J).filter (fun j => j ≤ n) = Finset.Icc 2 (min n J) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  calc occHtrunc J n = occH (min n J) := rfl
    _ = ∑ j ∈ Finset.Icc 2 (min n J), occW j := occH_eq_sum_occW (min n J)
    _ = ∑ j ∈ (Finset.Icc 2 J).filter (fun j => j ≤ n), occW j := by rw [hfilter]
    _ = ∑ j ∈ Finset.Icc 2 J, occW j * (if j ≤ n then (1 : ℝ) else 0) := by
        simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]

end Work.Deep.Sparse

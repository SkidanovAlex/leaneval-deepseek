import Mathlib
import Submission.Work.Peluse.Ulower.ss_aux_sum_subblock

namespace Work.Peluse.Ulower

/-- Decompose the block `[b+1, b+t*M]` into its `M` consecutive sub-blocks of length `t`, each
written as `{b+(m-1)t+r : r ∈ [1,t]}`. -/
theorem sum_Icc_subblock_decomp {t M b : ℕ} (ht : 1 ≤ t) (g : ℕ → ℂ) :
    ∑ y ∈ Finset.Icc (b + 1) (b + t * M), g y
      = ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 t, g (b + (m - 1) * t + r) := ss_aux_sum_subblock ht g

end Work.Peluse.Ulower

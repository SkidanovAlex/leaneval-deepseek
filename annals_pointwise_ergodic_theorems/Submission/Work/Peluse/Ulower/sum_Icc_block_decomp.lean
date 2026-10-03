import Mathlib
import Submission.Work.Peluse.Ulower.ss_aux_sum_block

namespace Work.Peluse.Ulower

/-- Split a sum over `[1,N] ⊆ ℕ` into the `J` consecutive blocks `[(j-1)L+1, jL]` (`j = 1..J`)
together with the remainder `[JL+1, N]`. -/
theorem sum_Icc_block_decomp {L J N : ℕ} (hL : 1 ≤ L) (hJ : J * L ≤ N) (g : ℕ → ℂ) :
    ∑ y ∈ Finset.Icc 1 N, g y
      = (∑ j ∈ Finset.Icc 1 J, ∑ y ∈ Finset.Icc ((j - 1) * L + 1) (j * L), g y)
        + ∑ y ∈ Finset.Icc (J * L + 1) N, g y := ss_aux_sum_block hL hJ g

end Work.Peluse.Ulower

import Mathlib
import Submission.Work.BW.mvdefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-- Subtracting the first (`k = 1`) term `ε cos(2πt)` from the Fourier series
`cosFourier ε t = ∑_{k≥1} (ε^k/k) cos(2πkt)` (the `k = 0` term vanishes) leaves the
tail `∑_{m≥0} (ε^(m+2)/(m+2)) cos(2π(m+2)t)`. -/
theorem cosFourier_sub_cos {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (t : ℝ) :
    cosFourier ε t - ε * Real.cos (2*Real.pi*t)
      = ∑' m : ℕ, (ε^(m+2)/((m:ℝ)+2)) * Real.cos (2*Real.pi*((m:ℝ)+2)*t) := by
  have hs := cosFourier_summable ε hε0 hε1 t
  have key := hs.sum_add_tsum_nat_add 2
  -- the partial sum over `i ∈ {0,1}` is exactly `ε cos(2πt)` (the `i = 0` term is `0`).
  have h2 : ∑ i ∈ Finset.range 2, (ε^i / ((i:ℕ):ℝ)) * Real.cos (2*Real.pi*((i:ℕ):ℝ)*t)
      = ε * Real.cos (2*Real.pi*t) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one]
    norm_num
  have hFS : (∑' i : ℕ, (ε^i / ((i:ℕ):ℝ)) * Real.cos (2*Real.pi*((i:ℕ):ℝ)*t))
        - ε * Real.cos (2*Real.pi*t)
      = ∑' i : ℕ, (ε^(i+2) / ((i+2:ℕ):ℝ)) * Real.cos (2*Real.pi*((i+2:ℕ):ℝ)*t) := by
    rw [h2] at key
    linarith
  rw [cosFourier, hFS]
  apply tsum_congr; intro m; norm_cast

end Work.BW

import Mathlib
import Submission.Work.BW.bpOddDefs
import Submission.Work.BW.num25_even

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Double-factorial growth, BW (25) step (iii): with `X = 2m`,
`4πX^{X−2}/e^X ≤ 2·(2m−1)!!(2m−3)!! = 2·bpNum m`. (Same content as the sibling node
`Work.BW.num25_even`, which is currently still `sorry`: if that node has been proved, derive this by
`simpa [bpNum]`; otherwise prove it directly.) Tight at `m = 1` (margin `e²/(2π) ≈ 1.176`), growing
in `m`. Suggested route: `bpNum m = ∏_{t=1}^{m−1}(4t²−1) ≥ 2^{2m−3}((m−1)!)²·(1/2)` from
`∏(1−1/(4t²)) ≥ 1 − (1/4)Σ_t 1/t² ≥ 1/2`, plus `(m−1)! ≥ (e²/2)m^{m−1}e^{−m}` (induction, base
`m = 2`, step needs `(1+1/m)^m ≤ e`), and `e⁴ ≥ 16π`. -/
theorem bpOdd_num25 (m : ℕ) (hm : 1 ≤ m) :
    4 * Real.pi * ((2*m : ℕ) : ℝ) ^ (2*m - 2) / Real.exp (((2*m : ℕ) : ℝ)) ≤ 2 * bpNum m := by
  simpa [bpNum, Nat.cast_mul] using num25_even m hm

end Work.BW

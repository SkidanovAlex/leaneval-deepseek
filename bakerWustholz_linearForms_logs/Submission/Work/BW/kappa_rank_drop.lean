import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `kappa n d ρ v c = (64 n d)^{r-ρ} · kappa n d r v c` for `ρ ≤ r ≤ n`.

*Proof:* `kappa n d r v c = (64nd)^{n-r} · K` with `K = (n!/2^{n-1}) · min(c/2^v) 1` independent of
`r`; `n - ρ = (n - r) + (r - ρ)` under `ρ ≤ r ≤ n`, then `pow_add`. -/
theorem kappa_rank_drop {n d r ρ v : ℕ} (c : ℝ) (hρr : ρ ≤ r) (hrn : r ≤ n) :
    kappa n d ρ v c = (64 * n * d : ℝ) ^ (r - ρ) * kappa n d r v c := by
  have hK : n - ρ = (n - r) + (r - ρ) := by omega
  unfold kappa
  rw [hK, pow_add]
  ring

end Work.BW

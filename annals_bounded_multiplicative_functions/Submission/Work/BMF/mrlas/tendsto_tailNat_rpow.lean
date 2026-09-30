import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF.mrlas

/-- For `σ > 1` the tail sum `∑_{k} (N + k)^{-σ}` tends to `0` as `N → ∞`.
In fact no hypothesis on `σ` is needed: for an arbitrary sequence `f : ℕ → ℝ` the
shifted tails `∑' k, f (k + i)` tend to `0` (`tendsto_sum_nat_add`), because
either the series is summable — in which case the tails are the remainders of a
convergent series — or it is not summable, in which case `tsum` is `0` by
convention. -/
theorem tendsto_tailNat_rpow (σ : ℝ) (hσ : 1 < σ) :
    Filter.Tendsto (fun N : ℕ => ∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ)) Filter.atTop (nhds 0) := by
  simpa only [Nat.add_comm] using
    (tendsto_sum_nat_add (f := fun m : ℕ => ((m : ℝ)) ^ (-σ)))

end Work.BMF.mrlas

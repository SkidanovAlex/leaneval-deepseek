import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pCoreSeries_one
import Submission.Work.Fitting.pLength_le_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pLength_eq_zero_iff`

For a finite `p`-solvable group `G`, the `p`-length of `G` vanishes exactly when `G` is
`p'`-closed, i.e. when `O_{p'}(G) = G`.

The `p`-length is half the least index `m` at which the upper `p`-series
`1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ ...` reaches `G`, and (by `pLength_le_iff`) the
condition `pLength p G ≤ n` is equivalent to the series being `⊤` at stage `2n + 1`.
Taking `n = 0`, the `p`-length is `0` iff the series is already `⊤` at stage `1`, and
that first stage is `O_{p'}(G)` (`pCoreSeries_one`).
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem pLength_eq_zero_iff (p : ℕ) (G : Type*) [Group G] [Finite G]
    (h : Work.Fitting.IsPSolvable p G) :
    Work.Fitting.pLength p G = 0 ↔ Work.Fitting.pPrimeCore p G = ⊤ := by
  rw [← Nat.le_zero, Work.Fitting.pLength_le_iff p G h 0,
    Work.Fitting.pCoreSeries_one]

end Work.Fitting

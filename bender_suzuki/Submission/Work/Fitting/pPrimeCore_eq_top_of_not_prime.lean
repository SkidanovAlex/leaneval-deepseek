import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_{p'}(G) = G` when `p` is not prime

If `p` is not a prime, every prime divisor of any natural number is different
from `p`, so `IsPiNat (· ≠ p) n` holds for *every* `n`.  Consequently the whole
group is a normal `p'`-subgroup and `O_{p'}(G) = G`.
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem pPrimeCore_eq_top_of_not_prime (p : ℕ) (G : Type*) [Group G] (hp : ¬ p.Prime) :
    Work.Fitting.pPrimeCore p G = ⊤ := by
  refine le_antisymm le_top (le_piCore Subgroup.normal_top ?_)
  intro q hq _
  exact fun h => hp (h ▸ hq)

end Work.Fitting

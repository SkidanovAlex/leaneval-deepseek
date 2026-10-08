import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- `O_p(G)` is contained in every Sylow `p`-subgroup of `G`.

`O_p(G)` is the supremum of the normal `p`-subgroups of `G`, and a normal `p`-subgroup
of `G` is contained in every Sylow `p`-subgroup by maximality of the latter
(`IsPGroup.le_sylow_of_normal`). -/
theorem pCore_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : Work.Fitting.pCore p G ≤ P := by
  rw [Work.Fitting.pCore, Work.Fitting.piCore]
  refine sSup_le fun N hN => ?_
  exact @IsPGroup.le_sylow_of_normal p G _ N hN.1
    (Work.Fitting.isPiNat_prime_iff_isPGroup Fact.out N |>.mp hN.2) P

end Work.Fitting

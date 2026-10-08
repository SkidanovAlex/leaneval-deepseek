import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pCore_le_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- `O_p(G) = G` if and only if `G` is a `p`-group.

`O_p(G)` is the largest normal `p`-subgroup of `G`.  If `O_p(G) = G` then, `O_p(G)`
being contained in every Sylow `p`-subgroup `P`, we get `P = G`, so `G` is a `p`-group.
Conversely if `G` is a `p`-group then `⊤` is a normal `p`-subgroup and hence is contained
in `O_p(G)`. -/
theorem pCore_eq_top_iff (p : ℕ) (G : Type*) [Group G] [Finite G] (hp : p.Prime) :
    Work.Fitting.pCore p G = ⊤ ↔ IsPGroup p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hP : (P : Subgroup G) = ⊤ := top_le_iff.mp (h ▸ pCore_le_sylow P)
    have hpg : IsPGroup p ↥(P : Subgroup G) := P.isPGroup'
    rw [hP] at hpg
    exact hpg.of_equiv Subgroup.topEquiv
  · intro h
    refine le_antisymm le_top ?_
    refine le_piCore (N := (⊤ : Subgroup G)) Subgroup.normal_top ?_
    exact (isPiNat_prime_iff_isPGroup hp ⊤).mpr (h.of_equiv Subgroup.topEquiv.symm)

end Work.Fitting

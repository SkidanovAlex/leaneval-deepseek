import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pCore_le_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_p(G)` is the intersection of the Sylow `p`-subgroups

For a finite group `G` and a prime `p`,

  `O_p(G) = ⋂_{P ∈ Sylow_p(G)} P`,

the largest normal `p`-subgroup of `G` is the intersection of all the Sylow `p`-subgroups.

The inclusion `O_p(G) ≤ P` for each Sylow `P` is `pCore_le_sylow`.  For the converse,
put `N = ⋂ P`.  Conjugation permutes the Sylow `p`-subgroups, hence fixes `N`, so `N` is
normal; and `N ≤ P` for any one Sylow `P` exhibits `N` as a `p`-group.  Being a normal
`p`-subgroup, `N` is contained in `O_p(G)`.
-/

open scoped Pointwise

namespace Work.Fitting

theorem pCore_eq_iInf_sylow (G : Type*) [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.Fitting.pCore p G = ⨅ P : Sylow p G, (P : Subgroup G) := by
  refine le_antisymm (le_iInf fun P => pCore_le_sylow P) ?_
  set N : Subgroup G := ⨅ P : Sylow p G, (P : Subgroup G) with hNdef
  -- `N` is normal: conjugation permutes the Sylow `p`-subgroups, hence fixes their intersection.
  have hNnormal : N.Normal := by
    rw [hNdef]
    refine Subgroup.Normal.of_conjugate_fixed fun g => ?_
    have hstep : MulAut.conj g • (⨅ P : Sylow p G, (P : Subgroup G)) =
        ⨅ P : Sylow p G, ↑(g • P) := by
      change Subgroup.map (↑(MulAut.conj g) : G →* G)
          (⨅ P : Sylow p G, (P : Subgroup G)) = _
      rw [Subgroup.map_iInf (↑(MulAut.conj g) : G →* G) (MulAut.conj g).injective]
      exact iInf_congr fun P => Sylow.coe_subgroup_smul.symm
    have hstep2 : (⨅ P : Sylow p G, (↑(g • P) : Subgroup G)) =
        ⨅ Q : Sylow p G, (Q : Subgroup G) := by
      refine le_antisymm ?_ ?_
      · refine le_iInf fun Q => ?_
        have h := iInf_le (f := fun P : Sylow p G => (↑(g • P) : Subgroup G)) (g⁻¹ • Q)
        rwa [smul_inv_smul] at h
      · exact le_iInf fun P => iInf_le _ (g • P)
    rw [hstep, hstep2]
  -- `N` is contained in a Sylow `p`-subgroup, hence is a `p`-group.
  have hNpg : IsPGroup p N := by
    obtain ⟨P0⟩ := Sylow.nonempty (p := p) (G := G)
    exact P0.isPGroup'.to_le (iInf_le (fun P : Sylow p G => (P : Subgroup G)) P0)
  exact le_piCore hNnormal ((isPiNat_prime_iff_isPGroup Fact.out N).mpr hNpg)

end Work.Fitting

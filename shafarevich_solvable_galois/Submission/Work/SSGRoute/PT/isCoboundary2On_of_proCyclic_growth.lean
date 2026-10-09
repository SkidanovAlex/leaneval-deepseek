import Mathlib
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **Vanishing of `H²` for a pro-cyclic group growing `p`-adically.**

On a compact topological group `Γ` all of whose finite quotients are cyclic, and which has open
normal subgroups of index divisible by `p` below every open normal subgroup, every locally
constant `2`-cocycle with values in a finite `𝔽_p`-module `N` (the `Γ`-action factoring through
`act : Γ →* G` and being trivial on some open subgroup of `Γ`) is the coboundary of a locally
constant `1`-cochain.

This is `Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth` with the pro-cyclicity hypothesis
spelled as `Work.SSGRoute.IsProCyclicGrp` (an `abbrev` for `NK.LocalTame.IsProCyclic`, i.e.
exactly "every finite quotient is cyclic"). -/
theorem isCoboundary2On_of_proCyclic_growth
    (p : ℕ) [Fact p.Prime] {Γ G N : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [Group G] [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N]
    (act : Γ →* G)
    (hker : ∃ U₀ : Subgroup Γ, IsOpen (U₀ : Set Γ) ∧ ∀ g ∈ U₀, ∀ n : N, act g • n = n)
    (hcyc : Work.SSGRoute.IsProCyclicGrp Γ)
    (hgrowth : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → U.Normal →
      ∃ V : Subgroup Γ, V ≤ U ∧ IsOpen (V : Set Γ) ∧ V.Normal ∧ p ∣ (V.subgroupOf U).index)
    (c : Γ → Γ → N) (hc : SSGRoute.IsCocycle2 act c)
    (hlc : SSGRoute.IsLocConst2 c) :
    SSGRoute.IsCoboundary2On act ⊤ c := by
  have hcyc' : ∀ (U : Subgroup Γ) [U.Normal], U.FiniteIndex → IsCyclic (Γ ⧸ U) := hcyc
  exact Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth p act hcyc' hker hgrowth c hc hlc

end Work.SSGRoute.PT

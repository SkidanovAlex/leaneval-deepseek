import Mathlib
import Submission.Work.CORE3.Defs

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Universal property of `O_p(K)` for a subgroup `K` of an ambient group: a subgroup `N ≤ K`
which is normal in `K` (i.e. `K` normalizes `N`) and a `p`-group lies in `pCoreIn p K`. -/
theorem LePCoreInOfNormal {G : Type} [Group G] {p : ℕ} {K N : Subgroup G}
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup p N) :
    N ≤ pCoreIn p K := by
  -- Viewing `N` inside `K`: the hypothesis `K ≤ N_G(N)` says exactly that `N ⊴ ↥K`.
  have hnorm : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hNK).mpr fun h k hh hk =>
      ((Subgroup.mem_normalizer_iff.mp (hKN hk)) h).mp hh
  -- and `N.subgroupOf K` is again a `p`-group, being isomorphic to `N` (`N ≤ K`).
  have hpg : IsPGroup p (N.subgroupOf K) :=
    IsPGroup.of_equiv hN (Subgroup.subgroupOfEquivOfLe hNK).symm
  -- A normal `p`-subgroup of `↥K` lies in `O_p(K)`: this is the defining universal property
  -- of `O_p(K) = normalCore (sSup {M ⊴ ↥K | M a p-group})`.
  have hle : N.subgroupOf K ≤ pCore p K := by
    haveI := hnorm
    exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hnorm, hpg⟩)
  -- Mapping back along `K.subtype`, which is injective with range `K ⊇ N`, gives the claim.
  have hmap : (N.subgroupOf K).map K.subtype = N := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNK]
  calc N = (N.subgroupOf K).map K.subtype := hmap.symm
    _ ≤ (pCore p K).map K.subtype := Subgroup.map_subtype_le_map_subtype.mpr hle

namespace Work.CORE3

/-- The same statement, exposed under the doubly nested name
`Work.CORE3.Work.CORE3.LePCoreInOfNormal` of the module's original skeleton. -/
theorem LePCoreInOfNormal {G : Type} [Group G] {p : ℕ} {K N : Subgroup G}
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup p N) :
    N ≤ pCoreIn p K :=
  _root_.Work.CORE3.LePCoreInOfNormal hNK hKN hN

end Work.CORE3

end Work.CORE3

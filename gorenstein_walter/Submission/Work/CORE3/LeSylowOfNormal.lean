import Mathlib
import Submission.Work.CORE3.Defs

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- A subgroup `N` which is normal in `K` and a `p`-group lies in every Sylow `p`-subgroup of `K`;
here the Sylow subgroup is given as a Sylow `p`-subgroup `P` of the ambient group with `P ≤ K`. -/
theorem LeSylowOfNormal {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K N : Subgroup G} (P : Sylow p G) (hPK : (P : Subgroup G) ≤ K)
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup p N) :
    N ≤ (P : Subgroup G) := by
  -- `P ≤ K` makes `P` a Sylow `p`-subgroup of `K`, and `K ≤ N_G(N)` makes `N` normal in `K`.
  have hNnorm : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKN
  have hNp : IsPGroup p (N.subgroupOf K) := hN.comap_subtype
  -- A normal `p`-subgroup lies in every Sylow `p`-subgroup of the ambient group.
  have hle : N.subgroupOf K ≤ ((P.subtype hPK : Sylow p K) : Subgroup K) :=
    IsPGroup.le_sylow_of_normal hNp (P.subtype hPK)
  rw [Sylow.coe_subtype] at hle
  intro x hx
  have hxK : x ∈ K := hNK hx
  have hx' : (⟨x, hxK⟩ : K) ∈ P.subgroupOf K :=
    hle (by rwa [Subgroup.mem_subgroupOf])
  rwa [Subgroup.mem_subgroupOf] at hx'

namespace Work.CORE3

/-- The same statement, exposed under the doubly nested name
`Work.CORE3.Work.CORE3.LeSylowOfNormal` of the module's original skeleton. -/
theorem LeSylowOfNormal {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K N : Subgroup G} (P : Sylow p G) (hPK : (P : Subgroup G) ≤ K)
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup p N) :
    N ≤ (P : Subgroup G) :=
  _root_.Work.CORE3.LeSylowOfNormal P hPK hNK hKN hN

end Work.CORE3

end Work.CORE3

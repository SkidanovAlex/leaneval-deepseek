import Mathlib
import Submission.Work.CORE2B.HallPerPrime_Xodd
import Submission.Work.CORE2B.Core18IsPGroupPCoreIn

namespace Work.CORE2B

open Subgroup

set_option linter.style.haveILetI false

/-- `O_p(K)` is contained in every `p`-subgroup `P ≤ K` whose relative index in `K` is not
divisible by `p` (i.e. in every Sylow `p`-subgroup of `K`). -/
theorem pCoreIn_le_of_relIndex_not_dvd {G : Type} [Group G] [Finite G] (p : ℕ) (hp : Nat.Prime p)
    {P K : Subgroup G} (hPK : P ≤ K) (hPp : IsPGroup p P) (hrel : ¬ p ∣ P.relIndex K) :
    Work.GW2.pCoreIn p K ≤ P := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Viewing `P` inside `K`: it is a `p`-subgroup of `K` of index prime to `p`.
  have hP'p : IsPGroup p (P.subgroupOf K) := hPp.comap_subtype
  have hrel' : ¬ p ∣ (P.subgroupOf K).index := hrel
  -- `O_p(K)` is a normal `p`-subgroup of `K`.
  have hsup : IsPGroup p ↥(sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}) :=
    Sylow.sSup_of_normal _ (fun N hN => hN.2) (fun N hN => hN.1)
  have hcoreP : IsPGroup p ↥(Work.GW2.pCore p K) :=
    hsup.to_le (Subgroup.normalCore_le _)
  -- A normal `p`-subgroup lies in every Sylow `p`-subgroup; `P` is Sylow in `K`.
  have hcore_le : Work.GW2.pCore p K ≤ P.subgroupOf K := by
    simpa using IsPGroup.le_sylow_of_normal hcoreP (hP'p.toSylow hrel')
  -- Transport back to `G`.
  rw [Work.GW2.pCoreIn, Subgroup.map_le_iff_le_comap]
  exact hcore_le

end Work.CORE2B

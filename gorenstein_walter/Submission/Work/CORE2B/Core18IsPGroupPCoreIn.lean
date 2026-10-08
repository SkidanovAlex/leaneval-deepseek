import Mathlib
import Submission.Work.CORE2B.Defs

/-!
# GW design 18, helper: `O_p(K)` is a `p`-group (public copy of the private
`Work.CORE2B.isPGroup_pCoreIn_gen`; importing BMAX's copy clashes `ASM.Defs` with `CORE2B.Defs`).
-/

namespace Work.GW18

theorem Core18IsPGroupPCoreIn {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (K : Subgroup G) : IsPGroup p ↥(Work.GW2.pCoreIn p K) := by
  have hsup : IsPGroup p ↥(sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}) :=
    Sylow.sSup_of_normal (G := ↥K) {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  have hcore : IsPGroup p (Work.GW2.pCore p ↥K) := hsup.to_le (Subgroup.normalCore_le _)
  unfold Work.GW2.pCoreIn
  exact hcore.map K.subtype

end Work.GW18

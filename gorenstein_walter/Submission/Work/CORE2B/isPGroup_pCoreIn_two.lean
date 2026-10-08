import Mathlib
import Submission.Work.CORE2B.Basic

namespace Work.CORE2B

open Subgroup

/-- **`O_2(M)` is a `2`-group.**  `pCoreIn 2 M` is the image in `G` of the normal core of the
supremum of the normal `2`-subgroups of `↥M`.  A supremum of normal `p`-subgroups is a `p`-group
(`Sylow.sSup_of_normal`), a subgroup of a `p`-group is a `p`-group (`IsPGroup.to_le`), and a
homomorphic image of a `p`-group is a `p`-group (`IsPGroup.map`). -/
theorem isPGroup_pCoreIn_two {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    IsPGroup 2 (Work.GW2.pCoreIn 2 M) := by
  have hsup : IsPGroup 2 ↥(sSup {N : Subgroup ↥M | N.Normal ∧ IsPGroup 2 N}) :=
    Sylow.sSup_of_normal (G := ↥M) (p := 2) {N : Subgroup ↥M | N.Normal ∧ IsPGroup 2 N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  have hcore : IsPGroup 2 (Work.GW2.pCore 2 ↥M) := hsup.to_le (Subgroup.normalCore_le _)
  unfold Work.GW2.pCoreIn
  exact hcore.map M.subtype

end Work.CORE2B

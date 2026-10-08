import Mathlib
import Submission.Work.GLUE.Defs

namespace Work.GLUE

/-- `Work.GW2.piCore π` is the supremum of the normal `π`-subgroups, wrapped in `normalCore`
(which is the identity because such a supremum is itself normal); `OddOrder.Isaacs.Ch03.oPiCore`
is the same supremum written as an `iSup` over the subtype of normal `π`-subgroups. The two
agree because `Subgroup.normalCore` fixes a normal subgroup. -/
theorem piCore_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    Work.GW2.piCore π G = OddOrder.Isaacs.Ch03.oPiCore π G := by
  apply le_antisymm
  · -- `π`-radical ≤ `O_π`: drop the `normalCore` and use that each normal `π`-subgroup is a
    -- generator of the `iSup` defining `oPiCore`.
    refine (Subgroup.normalCore_le _).trans ?_
    exact sSup_le (fun N hN =>
      le_iSup (fun H : {H : Subgroup G // H.Normal ∧
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π H} => (H.val : Subgroup G)) ⟨N, hN⟩)
  · -- `O_π` ≤ `π`-radical: `oPiCore` is normal and lies below the `sSup`, hence below its
    -- `normalCore` by maximality of the latter.
    refine Subgroup.normal_le_normalCore.mpr ?_
    exact iSup_le (fun H => le_sSup H.property)

end Work.GLUE

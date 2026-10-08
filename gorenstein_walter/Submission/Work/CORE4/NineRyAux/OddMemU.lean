import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.NineRyAux.OddSup

namespace Work.CORE4.NineRyAux

/-- If `H = U ⊔ S` with `U = O(H)` of odd order and `S` a `2`-group, then every element of `H`
of odd order already lies in `U`.  Indeed `H/U ≅ S/(S ∩ U)` is a `2`-group, so the image of an
odd-order element has odd order dividing a power of `2`, hence is trivial.

The element `x` is fed to the subgroup version `OddSup` through the cyclic subgroup `⟨x⟩`, whose
order is `orderOf x`. -/
theorem OddMemU {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (hH : B.H = B.U ⊔ (B.S : Subgroup G)) {x : G} (hx : x ∈ B.H) (hodd : Odd (orderOf x)) :
    x ∈ B.U := by
  -- `B.U = O(B.H) = oddCoreIn B.H` is normal in `↥B.H`, hence (using `hH`) in `B.U ⊔ B.S`.
  have hnorm : (B.U.subgroupOf (B.U ⊔ (B.S : Subgroup G))).Normal := by
    rw [← hH]
    have hUeq : B.U.subgroupOf B.H = Work.GW2.oddCore ↥B.H := by
      show (Work.GW2.oddCoreIn B.H).subgroupOf B.H = Work.GW2.oddCore ↥B.H
      rw [Work.GW2.oddCoreIn, Subgroup.subgroupOf]
      exact Subgroup.comap_map_eq_self_of_injective B.H.subtype_injective _
    rw [hUeq]
    exact Work.GW2.oddCore_normal ↥B.H
  have hoddX : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers]
    exact hodd
  have hXle : Subgroup.zpowers x ≤ B.U ⊔ (B.S : Subgroup G) :=
    Subgroup.zpowers_le.mpr (hH ▸ hx)
  exact OddSup hnorm B.S.isPGroup' hXle hoddX (Subgroup.mem_zpowers x)

end Work.CORE4.NineRyAux

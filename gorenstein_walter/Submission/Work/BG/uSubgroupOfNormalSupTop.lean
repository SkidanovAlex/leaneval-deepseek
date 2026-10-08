import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs

namespace Work.BG

/-- Let `D : Work.GW2.BGData G` with `D.U = O(H)` the odd core of `H = C_G(t)` (`D.U = (Work.GW2.oddCore ↥D.H).map D.H.subtype`). If `D.U ⊔ S = D.H` and `S ≤ C_G(t₁)`, then in the group `↥D.H` the subgroup `D.U` is normal and `D.U ⊔ C_H(t₁) = ⊤`. (Here `S ≤ H` holds because `S ≤ U ⊔ S = H`, and `U ⊔ C_H(t₁) ⊇ U ⊔ S = H`.)

Suggested route: `Subgroup.subgroupOf D.U D.H` is `(Work.GW2.oddCore ↥D.H).map D.H.subtype).comap D.H.subtype`, which equals `Work.GW2.oddCore ↥D.H` by `Subgroup.comap_map_eq_self_of_injective Subtype.val_injective` (since `subgroupOf` is `comap`), and `Work.GW2.oddCore_normal`; for the join use `Subgroup.map_injective D.H.subtype Subtype.val_injective` together with `Subgroup.map_sup`, `Subgroup.map_comap_eq`, `Subgroup.range_subtype`, reducing to `D.U ⊔ (D.H ⊓ C_G(t₁)) = D.H`. -/
theorem uSubgroupOfNormalSupTop {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (hUS : D.U ⊔ (D.S : Subgroup G) = D.H)
    (hSleC1 : (D.S : Subgroup G) ≤ Subgroup.centralizer ({D.t1} : Set G)) :
    (D.U.subgroupOf D.H).Normal ∧
      D.U.subgroupOf D.H ⊔ (Subgroup.centralizer ({D.t1} : Set G)).subgroupOf D.H = ⊤ := by
  refine ⟨?_, ?_⟩
  · -- `D.U = O(H).map subtype`, so its preimage in `↥D.H` is `O(H)` itself.
    have hsub : D.U.subgroupOf D.H = Work.GW2.oddCore ↥D.H :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    rw [hsub]
    exact Work.GW2.oddCore_normal ↥D.H
  · -- apply `map D.H.subtype`, injective, to both sides
    apply Subgroup.map_injective (f := D.H.subtype) Subtype.val_injective
    simp only [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype]
    -- reduced to `D.U ⊓ D.H ⊔ (C_G(t₁) ⊓ D.H) = D.H`
    have hUle : D.U ≤ D.H := Subgroup.map_subtype_le _
    have hSleH : (D.S : Subgroup G) ≤ D.H := by
      rw [← hUS]; exact le_sup_right
    rw [inf_eq_left.mpr hUle]
    refine le_antisymm (sup_le hUle inf_le_right) ?_
    calc D.H = D.U ⊔ (D.S : Subgroup G) := hUS.symm
      _ ≤ D.U ⊔ (Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H) :=
          sup_le le_sup_left ((le_inf hSleC1 hSleH).trans le_sup_right)

end Work.BG

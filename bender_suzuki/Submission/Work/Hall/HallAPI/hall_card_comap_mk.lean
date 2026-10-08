import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.HallAPI

/-- For `N ◁ G` and any subgroup `Hbar ≤ G ⧸ N`, the preimage of `Hbar` under the quotient
map is a union of `|Hbar|` cosets of `N`, hence has cardinality `|N| * |Hbar|`. -/
theorem hall_card_comap_mk {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (Hbar : Subgroup (G ⧸ N)) :
    Nat.card (Hbar.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card Hbar := by
  have hp : (fun x : G => x ∈ Hbar.comap (QuotientGroup.mk' N))
      = (fun x : G => QuotientGroup.mk x ∈ (Hbar : Set (G ⧸ N))) := by
    funext x; simp [QuotientGroup.mk'_apply, Subgroup.mem_comap]
  rw [show Nat.card (Hbar.comap (QuotientGroup.mk' N))
        = Nat.card (QuotientGroup.mk ⁻¹' (Hbar : Set (G ⧸ N))) from
      Nat.card_congr (Equiv.subtypeEquivProp hp)]
  rw [Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet N (Hbar : Set (G ⧸ N)))]
  rw [Nat.card_prod]
  rfl

end Work.Hall.HallAPI

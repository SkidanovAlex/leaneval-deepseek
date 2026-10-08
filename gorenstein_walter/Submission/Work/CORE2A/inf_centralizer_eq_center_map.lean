import Mathlib

namespace Work.CORE2A

theorem inf_centralizer_eq_center_map {K : Type} [Group K] (E : Subgroup K) :
    E ⊓ Subgroup.centralizer (E : Set K) = (Subgroup.center ↥E).map E.subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_map,
    Subgroup.mem_center_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨hxE, hx⟩
    exact ⟨⟨x, hxE⟩, fun y => Subtype.ext (hx y y.2), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun z hz => congrArg Subtype.val (hy ⟨z, hz⟩)⟩

end Work.CORE2A

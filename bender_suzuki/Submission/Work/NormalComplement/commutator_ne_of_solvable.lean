import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

theorem commutator_ne_of_solvable {G : Type*} [Group G] (E : Subgroup G) (hE : E ≠ ⊥) (hsol : Group.IsSolvable ↥E) : ⁅E, E⁆ ≠ E := by
  haveI := hsol
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hE
  -- Inside the group `↥E`, the commutator subgroup is a proper subgroup of the top.
  have htop : ⁅(⊤ : Subgroup ↥E), ⊤⁆ < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E
  -- Transport across `E.subtype`.
  have hmap : Subgroup.map E.subtype (⁅(⊤ : Subgroup ↥E), ⊤⁆)
      < Subgroup.map E.subtype (⊤ : Subgroup ↥E) :=
    (Subgroup.map_subtype_lt_map_subtype (G' := E)
      (H := ⁅(⊤ : Subgroup ↥E), ⊤⁆) (K := ⊤)).mpr htop
  have h1 : Subgroup.map E.subtype (⁅(⊤ : Subgroup ↥E), ⊤⁆) = ⁅E, E⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : Subgroup.map E.subtype (⊤ : Subgroup ↥E) = E := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rw [h1, h2] at hmap
  exact hmap.ne

end Work.NormalComplement

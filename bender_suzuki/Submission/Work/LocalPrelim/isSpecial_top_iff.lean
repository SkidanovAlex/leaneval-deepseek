import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Symplectic.conclusion_map_subtype

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `IsSpecial q ⊤` (in `↥G`) versus `IsSpecial q G` (in the ambient group)

For a subgroup `G ≤ X`, the property `Work.PGroup.IsSpecial q G` (stated in the ambient group `X`)
and the property `Work.PGroup.IsSpecial q (⊤ : Subgroup ↥G)` (stated in the group `↥G`) are
equivalent: the subgroup `⊤ ≤ ↥G` and the subgroup `G ≤ X` correspond under the inclusion
`G.subtype : ↥G →* X`, and `Work.PGroup.IsSpecial` is insensitive to that identification.

The forward direction is the existing
`Work.PGroup.Symplectic.ConclusionMapSubtype.isSpecial_map_subtype` at `X = ⊤`
(together with `(⊤ : Subgroup ↥G).map G.subtype = G`); the reverse direction is the new
`isSpecial_map_subtype_iff` below, which upgrades `isSpecial_map_subtype` to an equivalence.
-/

open scoped Classical Pointwise
open Subgroup

namespace Work.LocalPrelim

namespace IsSpecialTopAux

/-- The map `X ↦ X.map P.subtype` identifies the subgroup lattice of `↥P` with the interval
`{Y : Subgroup A // Y ≤ P}`, and this identification respects `Work.PGroup.IsSpecial`.  This
upgrades `Work.PGroup.Symplectic.ConclusionMapSubtype.isSpecial_map_subtype` to an equivalence. -/
theorem isSpecial_map_subtype_iff {A : Type*} [Group A] {P : Subgroup A} (p : ℕ)
    (X : Subgroup ↥P) :
    Work.PGroup.IsSpecial p X ↔ Work.PGroup.IsSpecial p (X.map P.subtype) := by
  refine ⟨Work.PGroup.Symplectic.ConclusionMapSubtype.isSpecial_map_subtype X, ?_⟩
  intro h
  rcases h with hea | ⟨hp, hnab, hcen, hfr, hcea⟩
  · exact Or.inl
      ((Work.PGroup.Symplectic.ConclusionMapSubtype.isElementaryAbelian_map_subtype_iff p X).mp
        hea)
  · refine Or.inr ⟨
      (Work.PGroup.Symplectic.ConclusionMapSubtype.isPGroup_map_subtype_iff p X).mp hp, ?_, ?_,
      ?_, ?_⟩
    · intro hc
      exact hnab
        ((Work.PGroup.Symplectic.ConclusionMapSubtype.isMulCommutative_map_subtype_iff X).mpr hc)
    · apply Subgroup.map_injective P.subtype_injective
      rw [← Work.PGroup.Symplectic.ConclusionMapSubtype.centerIn_map_subtype X,
        Subgroup.map_commutator, hcen]
    · apply Subgroup.map_injective P.subtype_injective
      rw [← Work.PGroup.Symplectic.ConclusionMapSubtype.centerIn_map_subtype X,
        ← Work.PGroup.Symplectic.ConclusionMapSubtype.frattiniIn_map_subtype X, hfr]
    · exact
        (Work.PGroup.Symplectic.ConclusionMapSubtype.isElementaryAbelian_map_subtype_iff p
          (Work.PGroup.centerIn X)).mp
          (by rw [← Work.PGroup.Symplectic.ConclusionMapSubtype.centerIn_map_subtype X]; exact hcea)

end IsSpecialTopAux

theorem isSpecial_top_iff {X : Type*} [Group X] {q : ℕ} (G : Subgroup X) :
    Work.PGroup.IsSpecial q (⊤ : Subgroup ↥G) ↔ Work.PGroup.IsSpecial q G := by
  have h := IsSpecialTopAux.isSpecial_map_subtype_iff (P := G) q (⊤ : Subgroup ↥G)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  exact h

end Work.LocalPrelim

import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.LocalPrelim.isSpecial_top_iff
import Submission.Work.PGroup.Symplectic.conclusion_map_subtype

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.AppVII

open scoped Classical Pointwise
open Subgroup

/-! The three transfers of `Work.PGroup.IsExtraspecial` between a subgroup `Q ≤ A` and the top
subgroup of `↥Q`. -/
namespace IsExtraspecialTransferAux

variable {A : Type*} [Group A]

/-- The preimage of `Q` under `Q.subtype` is `⊤`: commutative-ness transfers. -/
theorem isMulCommutative_top_iff (Q : Subgroup A) :
    IsMulCommutative ↥(⊤ : Subgroup ↥Q) ↔ IsMulCommutative ↥Q := by
  have h := Work.PGroup.Symplectic.ConclusionMapSubtype.isMulCommutative_map_subtype_iff
    (P := Q) (⊤ : Subgroup ↥Q)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  exact h.symm

/-- The centre of `⊤ ≤ ↥Q` and the centre of `Q ≤ A` have the same cardinality. -/
theorem card_centerIn_top (Q : Subgroup A) :
    Nat.card (Work.PGroup.centerIn (⊤ : Subgroup ↥Q)) =
      Nat.card (Work.PGroup.centerIn Q) := by
  have h := Work.PGroup.Symplectic.ConclusionMapSubtype.centerIn_map_subtype
    (P := Q) (⊤ : Subgroup ↥Q)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  rw [h, Subgroup.card_map_of_injective Q.subtype_injective]

end IsExtraspecialTransferAux

/-- Extraspecialness transfers between a subgroup `Q ≤ A` and the top subgroup of the group `↥Q`:
`Q` is extraspecial (as a subgroup of `A`) if and only if `⊤ ≤ ↥Q` is extraspecial.

Recall `Work.PGroup.IsExtraspecial q H = ¬ IsMulCommutative ↥H ∧ Work.PGroup.IsSpecial q H ∧
Nat.card ↥(Work.PGroup.centerIn H) = q`, so this is the conjunction of the three transfers
`IsMulCommutative ↥(⊤ : Subgroup ↥Q) ↔ IsMulCommutative ↥Q` (via `Subgroup.topEquiv`,
`isMulCommutative_map_subtype_iff`), `IsSpecial q (⊤ : Subgroup ↥Q) ↔ IsSpecial q (Q : Subgroup A)`
(via the identification of `↥(⊤ : Subgroup ↥Q)` with `↥Q`, which also identifies the Frattini
subgroups and centres; cf. `isSpecial_top_iff`), and
`Nat.card ↥(Work.PGroup.centerIn (⊤ : Subgroup ↥Q)) = Nat.card ↥(Work.PGroup.centerIn (Q : Subgroup A))`
(cf. `centerIn_map_subtype`). -/
theorem IsExtraspecialTransfer {A : Type*} [Group A] (Q : Subgroup A) {q : ℕ} :
    Work.PGroup.IsExtraspecial q (⊤ : Subgroup ↥Q) ↔ Work.PGroup.IsExtraspecial q Q := by
  constructor
  · intro h
    have h' := Work.PGroup.Symplectic.ConclusionMapSubtype.isExtraspecial_map_subtype
      (P := Q) (⊤ : Subgroup ↥Q) h
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h'
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro hc
      exact h.1 ((IsExtraspecialTransferAux.isMulCommutative_top_iff Q).mp hc)
    · exact (Work.LocalPrelim.isSpecial_top_iff Q).mpr h.2.1
    · rw [IsExtraspecialTransferAux.card_centerIn_top Q]
      exact h.2.2

end Work.NormalComplement.AppVII

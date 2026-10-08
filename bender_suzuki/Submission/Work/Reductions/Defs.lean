import Mathlib
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `Reductions`: local vocabulary

This file holds the small amount of notation the Bender--Suzuki reduction chapter needs
beyond `Submission/Blueprint/Interfaces.lean` (which it re-exports, so importing this module
gives access to `IsStronglyEmbedded`, `oddCore`, `oddResidual`, `HasFourGroup`,
`BenderConclusion`, `ThmBBelow`, `ThmAProp`, `FeitThompsonProp`, `IsAbelianSubgroup`, ...).

The main new notion is `HasFourGroupIn H`: `H` (a subgroup of an ambient group `G`) contains a
four-group of `G`, i.e. two distinct commuting involutions of `G` lying in `H`.  This is the
ambient-group version of `HasFourGroup` and is what one needs when replacing `G` by a quotient
or a normal subgroup: four-groups of `G` survive in `G ⧸ N` for `N` of odd order, and every
four-group of `G` lies in a conjugate of a strongly embedded subgroup.
-/

set_option autoImplicit false

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.Reductions

/-- `H` contains a four-group of the ambient group: two distinct commuting involutions of the
ambient group which both lie in `H`. -/
def HasFourGroupIn {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∃ a b : G, a ∈ H ∧ b ∈ H ∧ orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a

theorem HasFourGroupIn.mono {G : Type} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (h : HasFourGroupIn H) : HasFourGroupIn K := by
  obtain ⟨a, b, ha, hb, h1, h2, h3, h4⟩ := h
  exact ⟨a, b, hHK ha, hHK hb, h1, h2, h3, h4⟩

theorem HasFourGroupIn.to_subgroup {G : Type} [Group G] {H : Subgroup G}
    (h : HasFourGroupIn H) : HasFourGroup ↥H := by
  obtain ⟨a, b, ha, hb, h1, h2, h3, h4⟩ := h
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact h1
  · rw [Subgroup.orderOf_mk]; exact h2
  · intro hh; exact h3 (Subtype.ext_iff.mp hh)
  · exact Subtype.ext (by simpa using h4)

theorem HasFourGroupIn.of_subgroup {G : Type} [Group G] {H : Subgroup G}
    (h : HasFourGroup ↥H) : HasFourGroupIn H := by
  obtain ⟨a, b, h1, h2, h3, h4⟩ := h
  refine ⟨(a : G), (b : G), a.2, b.2, ?_, ?_, ?_, ?_⟩
  · rwa [Subgroup.orderOf_coe]
  · rwa [Subgroup.orderOf_coe]
  · intro hh; exact h3 (Subtype.ext hh)
  · exact congrArg (Subtype.val) h4

/-- A four-group of `G` whose three involutions lie in `H`. -/
theorem HasFourGroupIn.of_hasFourGroup {G : Type} [Group G] {H : Subgroup G}
    (hinv : ∀ x : G, orderOf x = 2 → x ∈ H) (h : HasFourGroup G) : HasFourGroupIn H := by
  obtain ⟨a, b, h1, h2, h3, h4⟩ := h
  exact ⟨a, b, hinv a h1, hinv b h2, h1, h2, h3, h4⟩

end Work.Reductions

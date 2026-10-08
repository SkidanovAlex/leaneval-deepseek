import Mathlib
import Submission.Work.Endgame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `HasFourGroup` is invariant under group isomorphism

`HasFourGroup G` (2-rank `≥ 2`) says that `G` contains two distinct commuting involutions.
A group isomorphism preserves element orders (`MulEquiv.orderOf_eq`), multiplication
(`MulEquiv.map_mul`) and injectivity, hence carries a four-group in `G` to one in `H` and
back along the inverse equivalence.
-/

namespace Work.Endgame

/-- A group isomorphism carries a four-group to a four-group. -/
theorem hasFourGroup_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Submission.Blueprint.HasFourGroup G) : Submission.Blueprint.HasFourGroup H := by
  obtain ⟨a, b, ha, hb, hne, hcomm⟩ := h
  exact ⟨e a, e b, by rw [MulEquiv.orderOf_eq, ha], by rw [MulEquiv.orderOf_eq, hb],
    fun h => hne (e.injective h), by rw [← e.map_mul, ← e.map_mul, hcomm]⟩

theorem hasFourGroup_iff_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) : Submission.Blueprint.HasFourGroup G ↔ Submission.Blueprint.HasFourGroup H :=
  ⟨fun h => hasFourGroup_of_mulEquiv e h, fun h => hasFourGroup_of_mulEquiv e.symm h⟩

end Work.Endgame

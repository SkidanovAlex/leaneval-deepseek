import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSHallW.PGroup

theorem inf_center_ne_bot_of_normal_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {N : Subgroup P} (hN : N.Normal) (hNne : N ≠ ⊥) :
    N ⊓ Subgroup.center P ≠ ⊥ := by
  -- A finite `p`-group is nilpotent, and in a nilpotent group every nontrivial
  -- normal subgroup meets the center.
  exact @Group.IsNilpotent.inf_center_ne_bot_of_normal P _ hP.isNilpotent N hN hNne

end Work.BSHallW.PGroup

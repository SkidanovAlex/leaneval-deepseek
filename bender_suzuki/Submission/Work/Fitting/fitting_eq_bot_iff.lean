import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- For a finite solvable group, the Fitting subgroup is trivial if and only if the group
itself is trivial: a nontrivial finite solvable group always contains a nontrivial normal
nilpotent subgroup (the last non-vanishing term of its derived series), so `F(G) ≠ ⊥`. -/
theorem fitting_eq_bot_iff (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] :
    Work.Fitting.fitting G = ⊥ ↔ Subsingleton G := by
  constructor
  · intro h
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    exact Work.Fitting.fitting_ne_bot G h
  · intro h
    refine le_antisymm (fun x _ => ?_) bot_le
    exact Subgroup.mem_bot.mpr (@Subsingleton.elim G h x 1)

end Work.Fitting

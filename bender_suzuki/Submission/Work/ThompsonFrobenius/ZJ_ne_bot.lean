import Mathlib
import Submission.Work.ThompsonFrobenius.BlueprintZJ
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThompsonFrobenius

/-- `ZJ(P) = Z(J(P))` is nontrivial for a nontrivial finite `p`-group `P`.

Mathematically: a nontrivial finite `p`-group has nontrivial centre, so `Z(P) ≠ ⊥`; the centre
of `P` is contained in `ZJ(P)` (`Work.PGroup.centerIn_le_ZJ`), whence `ZJ(P) ≠ ⊥`.  The bridge
`Submission.Blueprint.ZJ P = Work.PGroup.ZJ P` is `Work.GlaubermanZJ.ZJ_eq`, and the nonvanishing
of the centre follows from the fixed-point argument `Work.PGroup.inf_centralizer_ne_bot_of_isPGroup`
applied to the conjugation action of `P` on itself. -/
theorem ZJ_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P) (hne : P ≠ ⊥) : Submission.Blueprint.ZJ P ≠ ⊥ := by
  rw [Work.GlaubermanZJ.ZJ_eq P]
  have hcenter_ne : Work.PGroup.centerIn P ≠ ⊥ := by
    rw [Work.PGroup.centerIn_eq_inf_centralizer]
    exact Work.PGroup.inf_centralizer_ne_bot_of_isPGroup (Fact.out : p.Prime) P P hP hP hne
      Subgroup.le_normalizer
  intro hbot
  exact hcenter_ne (le_bot_iff.mp (hbot ▸ Work.PGroup.centerIn_le_ZJ P))

end Work.ThompsonFrobenius

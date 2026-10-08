import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.centerIn_le_ZJ
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

-- Non-vacuity of the area's theorem: `Z(J(P)) ≠ 1` for a nontrivial finite `p`-group `P`
-- with `p` prime (because `Z(P) ≠ 1` for such a group and `Z(P) ≤ Z(J(P))`,
-- `Work.GlaubermanZJ.centerIn_le_ZJ`).
theorem ZJ_ne_bot {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (P : Subgroup G) [Finite P]
    (hPp : IsPGroup p P) (hP : P ≠ ⊥) : Submission.Blueprint.ZJ P ≠ ⊥ := by
  have hpprime : Fact p.Prime := ⟨hp⟩
  -- `P` is a nontrivial finite `p`-group, so its centre is nontrivial.
  have hnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  have hcenter : ⊥ < Subgroup.center ↥P := IsPGroup.bot_lt_center hPp
  have hcenter_ne : Subgroup.center ↥P ≠ ⊥ := bot_lt_iff_ne_bot.mp hcenter
  -- hence `Z(P) = centerIn P ≠ ⊥`.
  have hmap : Work.PGroup.centerIn P ≠ ⊥ := by
    show (Subgroup.center ↥P).map P.subtype ≠ ⊥
    intro h
    exact hcenter_ne
      (Subgroup.map_injective (Subgroup.subtype_injective P) (by rw [Subgroup.map_bot, h]))
  -- `Z(P) ≤ Z(J(P))` and `Z(P) ≠ ⊥` give `Z(J(P)) ≠ ⊥`.
  intro hZJ
  have hle : Work.PGroup.centerIn P ≤ (⊥ : Subgroup G) := by
    have h := Work.GlaubermanZJ.centerIn_le_ZJ P
    rw [hZJ] at h
    exact h
  exact hmap (le_bot_iff.mp hle)

end Work.GlaubermanZJ

import Mathlib
import Submission.Work.SmallRank.Regular.Defs
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.SmallRank.Regular

theorem agemo_eq_bot_of_pow {G : Type*} [Group G] {p : ℕ} {K : Subgroup G}
    (h : ∀ g ∈ K, g ^ p = 1) : Work.PGroup.agemo p 1 K = ⊥ := by
  rw [Work.PGroup.agemo, ← le_bot_iff, Subgroup.closure_le]
  rintro y ⟨x, hx, rfl⟩
  simpa using h x hx

end Work.SmallRank.Regular
